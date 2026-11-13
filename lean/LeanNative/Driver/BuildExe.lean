import Lean
import Lean.Compiler.LCNF.EmitC
import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.IR.Bridge
import LeanNative.Transform.EqSat
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Plugins
import LeanNative.Backend.LLVM
import LeanNative.Backend.FastCheck

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

/-- Decide whether native executable linking uses standalone static `libleanrt.a` + `libInit.a` (`true`)
    or shared `libleanshared` (`false`), failing closed when `--standalone` is explicitly requested
    alongside `--dynamic-runtime`, on Darwin, or when static runtime archives are missing. -/
def resolveStandaloneLinkMode (isDarwin forceStandalone forceDynamic hasStaticLeanRt hasStaticInit : Bool) :
    Except String Bool :=
  if forceStandalone && forceDynamic then
    .error "[lean-native] conflicting flags: `--standalone` and `--dynamic-runtime` cannot be combined"
  else if forceStandalone && isDarwin then
    .error "[lean-native] `--standalone` static runtime linking is not supported on Darwin targets"
  else if forceStandalone && (!hasStaticLeanRt || !hasStaticInit) then
    .error "[lean-native] `--standalone` requested, but static Lean runtime archives (`libleanrt.a`, `libInit.a`) are missing"
  else
    .ok (!isDarwin && !forceDynamic && hasStaticLeanRt && hasStaticInit)

/-- Resolve the Lean 4.35 sysroot path reliably even when `lean` is not on `PATH`. -/
def resolveLeanSysroot : IO System.FilePath := do
  if let some envRoot ← IO.getEnv "LEAN_SYSROOT" then
    if !envRoot.isEmpty then
      return System.FilePath.mk envRoot
  Lean.findSysroot

/-- When `filePath` (e.g., `SnarkFast/Kernels.lean`) is an umbrella module that re-exports
    domain submodules in `<filePath_without_.lean>/<Sub>.lean` (`Field`, `Ntt`, `Hashes`, `Pcs`),
    inline those local submodule sources (stripping their `import ` headers) so `Lean.Elab.runFrontend`
    elaborates all `@[export]` kernels in a single local LCNF unit. -/
private def expandUmbrellaSubmodules (filePath : String) (raw : String) : IO String := do
  if (System.FilePath.mk filePath).extension != some "lean" then return raw
  let subDir := System.FilePath.mk ((filePath.dropEnd 5).toString)
  if !(← subDir.pathExists) then return raw
  let stem := subDir.fileName.getD ""
  let mut outLines : Array String := #[]
  for line in raw.splitOn "\n" do
    let trimmed := line.trimAscii.toString
    if trimmed.startsWith "import " then
      let modPath := (trimmed.drop 7).trimAscii.toString
      let parts := modPath.splitOn "."
      match parts.reverse with
      | leaf :: parent :: _ =>
        let candPath := subDir / s!"{leaf}.lean"
        if parent == stem && (← candPath.pathExists) then
          let subRaw ← IO.FS.readFile candPath
          for subLine in subRaw.splitOn "\n" do
            if !subLine.trimAscii.toString.startsWith "import " then
              outLines := outLines.push subLine
        else
          outLines := outLines.push line
      | _ => outLines := outLines.push line
    else
      outLines := outLines.push line
  return String.intercalate "\n" outLines.toList

/-- Run `Lean.Elab.runFrontend` on `filePath` and execute `act` inside `CoreM`.
    Automatically includes `.lake/build/lib/lean` (populated by `turbo-lean build`'s
    transactional module-DAG publisher) and `build/olean` in the Lean search path. -/
def withElaboratedFrontend {α : Type} (filePath : String) (modName : Lean.Name) (act : Lean.CoreM α) : IO α := do
  let mut extraPaths : Lean.SearchPath := []
  for cand in [".lake/build/lib/lean", "build/olean"] do
    let p := System.FilePath.mk cand
    if ← p.pathExists then
      extraPaths := extraPaths ++ [p]
  Lean.initSearchPath (← resolveLeanSysroot) extraPaths
  let rawInput ← IO.FS.readFile filePath
  let input ← expandUmbrellaSubmodules filePath rawInput
  let opts : Lean.Options := {}
  let some env ← Lean.Elab.runFrontend input opts filePath modName
    | throw <| IO.userError s!"Elaboration failed for {filePath}"
  let coreCtx : Lean.Core.Context := { fileName := filePath, fileMap := filePath.toFileMap, options := opts }
  Prod.fst <$> act.toIO coreCtx { env := env }

/-- Elaborate a `.lean` source file and inline local calls while preserving every
    lowered declaration. An ABI symbol's spelling does not establish internal ownership. -/
def ingestLeanSourceFile (filePath : String) (moduleName : String := "LeanNative.FileInput")
    (arch : TargetArch := .x86_64) (allowRcAdt : Bool := false) : IO LNIRModule :=
  normalizeAndInlineLocalDefs <$> withElaboratedFrontend filePath `LeanNativeInput (ingestAllLocalDecls moduleName arch allowRcAdt)

def emitLeanCFromSourceFile (filePath : String) (modName : Lean.Name := `Main)
    (arch : TargetArch := .x86_64) : IO (String × LNIRModule × Array String) :=
  withElaboratedFrontend filePath modName do
    let env ← getEnv
    let names ← Lean.Compiler.LCNF.getLocalImpureDecls
    let mut selected := names.filter (fun n => (Lean.getExportNameFor? env n).isSome)
    for _ in [:names.size] do
      for n in selected do
        if let some d ← Lean.Compiler.LCNF.getLocalImpureDecl? n then
          if let .code c := d.value then
            for callee in collectCodeLocalCallees names c do
              if !selected.contains callee then selected := selected.push callee
    let mod ← ingestModuleDecls selected modName.toString arch
    let mut objects := #[]
    let sysroot ← resolveLeanSysroot
    for n in env.header.moduleNames do
      let olean ← Lean.findOLean n
      if !olean.toString.startsWith sysroot.toString then
        let obj := ((olean.toString.replace "/lib/lean/" "/ir/").dropEnd 6).toString ++ ".c.o.export"
        unless ← (System.FilePath.mk obj).pathExists do
          throwError "[lean-native] missing native object for imported module {n}: {obj}"
        objects := objects.push obj
    return (← Lean.Compiler.LCNF.emitC modName, mod, objects)

/-- P-cert C4/C5 `build-exe` gate (fail closed, checked before any file is written): the Bridge already refuses
    RC-ADT decls without `allowRcAdt`, but the LLVM backend accepts no heap code, so `build-exe` re-checks
    `findRcAdtDecl?` on the lowered module and `findUnsupportedLLVMCall?` on the optimized one explicitly. -/
def buildExeLLVMGate? (rawMod optMod : LNIRModule) (arch : TargetArch := .x86_64) : Option String :=
  (rawMod.findRcAdtDecl?.map fun d => s!"[lean-native] build-exe: RC-ADT declaration '{d}' is unsupported by the LLVM backend") <|>
  ((LeanNative.Backend.LLVM.findUnsupportedLLVMCall? optMod arch).map fun (d, c) =>
    s!"[lean-native] build-exe: unsupported external or non-scalar call '{c}' in '{d}'")

/-- Full LCNF-to-Executable builder (`buildNativeExecutable` / `buildExecutableFromLeanFile`). -/
def buildNativeExecutable (filePath : String) (outBin : String) (optLevel : String := "-O3")
    (cliArgs : List String := []) : IO (LNIRModule × String) := do
  let sysroot ← resolveLeanSysroot
  let hostArch : TargetArch :=
    if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then .arm64 else .x86_64
  let (cCode, rawMod, importObjects) ← emitLeanCFromSourceFile filePath `Main hostArch
  let (optMod, _) := LeanNative.Transform.runDefaultPipeline rawMod
  if let some err := buildExeLLVMGate? rawMod optMod hostArch then throw <| IO.userError err
  let superoptTgt : LeanNative.Transform.SuperoptTarget :=
    match hostArch with
    | .arm64 => .arm64
    | _ => .x86_64
  let batchEnv ← IO.getEnv "SANDBOXED_TELEMETRY_BATCH_ONLY"
  let isBatchOnly := (batchEnv.map (fun s => s.trimAscii.toString) |>.getD "") == "1"
  if !isBatchOnly then
    let telCfg ← LeanNative.Backend.FastCheck.TelemetryConfig.probe cliArgs
    if telCfg.enabled then
      let _ ← LeanNative.Transform.emitModuleTelemetryEvents telCfg superoptTgt false rawMod
  let lnirLlPath := s!"{outBin}.lnir.ll"
  let lnirLlText := LeanNative.Backend.LLVM.emitLLVMOptimized optMod hostArch
  IO.FS.writeFile lnirLlPath lnirLlText

  let cPath := s!"{outBin}.lean.c"
  let rawLlPath := s!"{outBin}.raw.ll"
  let optLlPath := s!"{outBin}.opt.ll"
  IO.FS.writeFile cPath cCode

  let incDir := (sysroot / "include").toString
  let clangIncDir := (sysroot / "include" / "clang").toString
  let libDir := (sysroot / "lib" / "lean").toString

  let runtimePath := s!"{outBin}.runtime.c"
  IO.FS.writeFile runtimePath LeanNative.Backend.LLVM.leanRuntimeC
  let sysClang : System.FilePath := "/usr/bin/clang"
  let tcClang : System.FilePath := sysroot / "bin" / "clang"
  let clangCmd ←
    if (← sysClang.pathExists) then pure sysClang.toString
    else if (← tcClang.pathExists) then pure tcClang.toString
    else pure "clang"
  let extraIncArgs : Array String :=
    if clangCmd == tcClang.toString then #[s!"-isystem{clangIncDir}"] else #[]

  let clangEmitOut ← IO.Process.output {
    cmd  := clangCmd
    args := #["-S", "-emit-llvm", optLevel, "-Xclang", "-disable-llvm-passes", "-DNDEBUG", "-march=native",
      s!"-I{incDir}"] ++ extraIncArgs ++ #[cPath, "-o", rawLlPath]
  }
  if clangEmitOut.exitCode != 0 then
    throw <| IO.userError s!"clang -emit-llvm failed:\n{clangEmitOut.stderr}"

  let mergedLlPath := s!"{outBin}.merged.ll"
  let mergeOut ← IO.Process.output {
    cmd := "llvm-link"
    args := #["-S", rawLlPath, s!"--override={lnirLlPath}", "-o", mergedLlPath]
  }
  if mergeOut.exitCode != 0 then
    throw <| IO.userError s!"LLVM optimized definition merge failed:\n{mergeOut.stderr}"

  let optOut ← IO.Process.output {
    cmd := "opt"
    args := #["-S", "-passes=default<O3>,loop-vectorize,slp-vectorizer", mergedLlPath, "-o", optLlPath]
  }
  if optOut.exitCode != 0 then
    throw <| IO.userError s!"LLVM optimization failed:\n{optOut.stderr}"

  let isDarwin := (System.Platform.target.splitOn "darwin").length > 1 || (System.Platform.target.splitOn "apple").length > 1
  let linkInputs := #[optLlPath, runtimePath] ++ importObjects
  let sysLibDir := (sysroot / "lib").toString
  let hasStaticLeanRt ← ((sysroot / "lib" / "lean" / "libleanrt.a").pathExists)
  let hasStaticInit ← ((sysroot / "lib" / "lean" / "libInit.a").pathExists)
  let hasStaticStd ← ((sysroot / "lib" / "lean" / "libStd.a").pathExists)
  let forceDynamic := cliArgs.contains "--dynamic-runtime"
  let forceStandalone := cliArgs.contains "--standalone"
  let useStandaloneStatic ← match resolveStandaloneLinkMode isDarwin forceStandalone forceDynamic hasStaticLeanRt hasStaticInit with
    | .ok mode => pure mode
    | .error msg => throw <| IO.userError msg
  let runtimeLinkFlags : Array String ← do
    if useStandaloneStatic then
      let leanLibDir := sysroot / "lib" / "lean"
      let mut leanArchives := #[(leanLibDir / "libInit.a").toString, (leanLibDir / "libLean.a").toString]
      if hasStaticStd then leanArchives := leanArchives.push (leanLibDir / "libStd.a").toString
      leanArchives := leanArchives.push (leanLibDir / "libleanrt.a").toString
      if (← (leanLibDir / "libleancpp.a").pathExists) then
        leanArchives := leanArchives.push (leanLibDir / "libleancpp.a").toString
      let mut extStatic := #[]
      for cand in #["libgmp.a", "libunwind.a", "libuv.a", "libc++.a", "libc++abi.a"] do
        if (← (sysroot / "lib" / cand).pathExists) then
          extStatic := extStatic.push (sysroot / "lib" / cand).toString
      pure (#[s!"-L{libDir}", s!"-L{sysLibDir}", "-Wl,--gc-sections", "-Wl,--start-group"] ++
        leanArchives ++ extStatic ++ #["-Wl,--end-group", "-lm", "-lpthread", "-ldl", "-lrt"])
    else
      pure #[s!"-L{libDir}", "-lleanshared", s!"-Wl,-rpath,{libDir}", "-lm", "-lpthread", "-ldl"]
  let linkWith (flags : Array String) := IO.Process.output {
    cmd := clangCmd
    args := #[optLevel, "-DNDEBUG", "-march=native", "-Wno-override-module", s!"-I{incDir}"] ++
      extraIncArgs ++ linkInputs ++ flags ++ #["-o", outBin]
  }
  let mut linkOut ← linkWith runtimeLinkFlags
  if linkOut.exitCode != 0 && useStandaloneStatic && !cliArgs.contains "--standalone" then
    linkOut ← linkWith #[s!"-L{libDir}", "-lleanshared", s!"-Wl,-rpath,{libDir}", "-lm", "-lpthread", "-ldl"]
  if linkOut.exitCode != 0 then
    throw <| IO.userError s!"clang native link failed:\n{linkOut.stderr}"

  return (optMod, lnirLlPath)

abbrev buildExecutableFromLeanFile := buildNativeExecutable

abbrev collatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev tupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev sarrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev dotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev saxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev matmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkCollatzStepsDecl : LNIRDecl := LeanNative.IR.Codec.collatzStepsDecl
abbrev mkTupleAccumSumDecl : LNIRDecl := LeanNative.IR.Codec.tupleAccumSumDecl
abbrev mkSArrayScaleBiasDecl : LNIRDecl := LeanNative.IR.Codec.sarrayScaleBiasDecl
abbrev mkDotProductU64Decl : LNIRDecl := LeanNative.IR.Codec.dotProductU64Decl
abbrev mkSaxpyKernelDecl : LNIRDecl := LeanNative.IR.Codec.saxpyKernelDecl
abbrev mkMatmulTiledU64Decl : LNIRDecl := LeanNative.IR.Codec.matmulTiledU64Decl
abbrev mkEvmErc20TransferU256Decl : LNIRDecl := LeanNative.IR.evmErc20TransferU256Decl
abbrev mkEvmMulDivWadU256Decl : LNIRDecl := LeanNative.IR.evmMuldivWadU256Decl
abbrev mkCanonicalBenchmarkModule : LNIRModule := LeanNative.IR.Codec.mkCanonicalBenchmarkModule

end LeanNative.IR
