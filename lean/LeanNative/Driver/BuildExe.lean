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

/-- Resolve the Lean 4.35 sysroot path reliably even when `lean` is not on `PATH`. -/
def resolveLeanSysroot : IO System.FilePath := do
  if let some envRoot ← IO.getEnv "LEAN_SYSROOT" then
    if !envRoot.isEmpty then
      return System.FilePath.mk envRoot
  try
    Lean.findSysroot
  catch _ =>
    let home := (← IO.getEnv "HOME").getD ""
    let candidates := [
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0",
      "/var/lib/orb-node/work/caches/elan/toolchains/leanprover--lean4---v4.35.0"
    ]
    for c in candidates do
      let p := System.FilePath.mk c
      if ← p.pathExists then
        return p
    return System.FilePath.mk "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0"

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
  (normalizeAndInlineLocalDefs · allowRcAdt) <$> withElaboratedFrontend filePath `LeanNativeInput (ingestAllLocalDecls moduleName arch allowRcAdt)

/-- Elaborate `filePath` with `Lean.Elab.runFrontend`, extracting both the Lean 4.31 C module code
    (`Lean.Compiler.LCNF.emitC modName`) and the lowered `LNIRModule` via `ingestAllLocalDecls`. -/
def emitLeanCFromSourceFile (filePath : String) (modName : Lean.Name := `Main)
    (arch : TargetArch := .x86_64) : IO (String × LNIRModule) :=
  withElaboratedFrontend filePath modName do
    let mod ← ingestAllLocalDecls modName.toString arch
    return (← Lean.Compiler.LCNF.emitC modName, mod)

/-- Full LCNF-to-Executable builder (`buildNativeExecutable` / `buildExecutableFromLeanFile`). -/
def buildNativeExecutable (filePath : String) (outBin : String) (optLevel : String := "-O3")
    (cliArgs : List String := []) : IO (LNIRModule × String) := do
  let sysroot ← resolveLeanSysroot
  let hostArch : TargetArch :=
    if System.Platform.target.startsWith "aarch64" || System.Platform.target.startsWith "arm64" then .arm64 else .x86_64
  let (cCode, rawMod) ← emitLeanCFromSourceFile filePath `Main hostArch
  let (optMod, _) := LeanNative.Transform.runDefaultPipeline rawMod
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
  let lnirOptLlPath := s!"{outBin}.lnir.opt.ll"
  let lnirLlText := LeanNative.Backend.LLVM.emitLLVMOptimized optMod hostArch
  IO.FS.writeFile lnirLlPath lnirLlText

  let cPath := s!"{outBin}.lean.c"
  let rawLlPath := s!"{outBin}.raw.ll"
  let optLlPath := s!"{outBin}.opt.ll"
  IO.FS.writeFile cPath cCode

  let incDir := (sysroot / "include").toString
  let clangIncDir := (sysroot / "include" / "clang").toString
  let libDir := (sysroot / "lib" / "lean").toString

  let relRuntime : System.FilePath := "runtime/lean_native_runtime.c"
  let absRuntime : System.FilePath := "/var/lib/spark-admin/jobs/3730b838-a03b-49e3-bbd2-eb51c132a4e7/lean-native/runtime/lean_native_runtime.c"
  let runtimePath ← if (← relRuntime.pathExists) then pure relRuntime.toString else pure absRuntime.toString
  let runtimeDir := ((System.FilePath.mk runtimePath).parent.getD (System.FilePath.mk "runtime")).toString
  let cOptScript : System.FilePath := ((System.FilePath.mk runtimeDir).parent.getD (System.FilePath.mk ".")) / "scripts" / "ln_c_opt.py"
  let cOptPath := if (← cOptScript.pathExists) then cOptScript.toString else "scripts/ln_c_opt.py"
  discard <| IO.Process.output { cmd := "python3", args := #[cOptPath, cPath, cPath] }

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
    args := #["-S", "-emit-llvm", optLevel, "-Xclang", "-disable-llvm-passes", "-DNDEBUG", "-march=native", s!"-I{incDir}", s!"-I{runtimeDir}"] ++ extraIncArgs ++ #[cPath, "-o", rawLlPath]
  }
  if clangEmitOut.exitCode != 0 then
    throw <| IO.userError s!"clang -emit-llvm failed:\n{clangEmitOut.stderr}"

  let intrDecls := optMod.decls.filter fun d =>
    ["l_clmul64Hi", "l_clmul64", "l_gf2Affine", "l_eor3"].any fun s => (d.name.splitOn s).length > 1
  if !intrDecls.isEmpty then
    let intrPath := s!"{outBin}.intr.ll"
    IO.FS.writeFile intrPath ((LeanNative.Backend.LLVM.emitLLVMOptimized { optMod with decls := intrDecls } hostArch).replace ") #0 {" ") alwaysinline #0 {")
    if (← (System.FilePath.mk "/usr/lib/llvm-18/bin/llvm-link").pathExists) then
      discard <| IO.Process.output { cmd := "/usr/lib/llvm-18/bin/llvm-link", args := #["-S", rawLlPath, s!"--override={intrPath}", "-o", rawLlPath] }
    else
      discard <| IO.Process.output { cmd := "python3", args := #[cOptPath, "--override-ll", rawLlPath, intrPath, rawLlPath] }

  let optBin : System.FilePath := "/usr/lib/llvm-18/bin/opt"
  let hasOptBin ← optBin.pathExists
  let runOptPass (inLl outLl : String) (fallback : IO String) : IO Unit := do
    if hasOptBin then
      try
        let out ← IO.Process.output {
          cmd  := optBin.toString
          args := #["-S", "-passes=default<O3>,loop-vectorize,slp-vectorizer", "-vectorize-loops", "-vectorize-slp", inLl, "-o", outLl]
        }
        if out.exitCode == 0 then return ()
      catch _ => pure ()
    try
      let clangIrOut ← IO.Process.output {
        cmd  := clangCmd
        args := #["-x", "ir", optLevel, "-S", "-emit-llvm", "-Wno-override-module", inLl, "-o", outLl]
      }
      if clangIrOut.exitCode != 0 then IO.FS.writeFile outLl (← fallback)
    catch _ =>
      IO.FS.writeFile outLl (← fallback)
  runOptPass rawLlPath optLlPath (IO.FS.readFile rawLlPath)
  runOptPass lnirLlPath lnirOptLlPath (pure lnirLlText)

  let isDarwin := (System.Platform.target.splitOn "darwin").length > 1 || (System.Platform.target.splitOn "apple").length > 1
  let linkInputs := if isDarwin then #[optLlPath, runtimePath] else #[optLlPath, lnirOptLlPath, runtimePath, "-Wl,--allow-multiple-definition"]
  let linkOut ← IO.Process.output {
    cmd  := clangCmd
    args := #[optLevel, "-DNDEBUG", "-march=native", "-Wno-override-module", s!"-I{incDir}", s!"-I{runtimeDir}"] ++
      extraIncArgs ++ linkInputs ++ #[s!"-L{libDir}", "-lleanshared", s!"-Wl,-rpath,{libDir}", "-lm", "-lpthread", "-ldl", "-o", outBin]
  }
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
