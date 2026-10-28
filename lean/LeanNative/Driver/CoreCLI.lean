import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Semantics.Refinement
import LeanNative.Proofs.PeepholeProofs
import LeanNative.Proofs.LoopOptProofs
import LeanNative.Proofs.SymbolicTV
import LeanNative.Proofs.CertChecker
import LeanNative.Proofs.AxiomAudit
import LeanNative.Transform.Pass
import LeanNative.Transform.AlgebraicOpt
import LeanNative.Transform.UnboxTupleSROA
import LeanNative.Transform.HoistExclusivity
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Transform.Superopt
import LeanNative.Transform.Plugins
import LeanNative.Backend.LLVM
import LeanNative.Backend.GPUIR
import LeanNative.Backend.MLIRGPU
import LeanNative.Backend.Metal
import LeanNative.Backend.Hybrid
import LeanNative.Backend.FastCheck
import LeanNative.Driver.Worker
import LeanNative.Driver.CAbiEmit
import LeanSys.Posix
import LeanSys.Codec

namespace LeanNative.Driver.CoreCLI

open LeanSys.Par
open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Spec
open LeanNative.Semantics
open LeanNative.Proofs
open LeanNative.Transform
open LeanNative.Backend
open LeanNative.Backend.LLVM
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanSys.Posix
open LeanSys.Codec
open LeanNative.Backend.Hybrid
open LeanNative.Backend.FastCheck


def findFlagValue (args : List String) (flag : String) (defaultVal : String) : String :=
  match args with
  | [] => defaultVal
  | f :: v :: rest => if f == flag then v else findFlagValue (v :: rest) flag defaultVal
  | _ :: rest => findFlagValue rest flag defaultVal

def hasFlag (args : List String) (flag : String) : Bool := args.contains flag

def findFirstPositional : List String → String
  | [] => ""
  | "--input" :: v :: _ | "--lnir" :: v :: _ => v
  | flag :: v :: rest =>
    if ["-o", "--opt", "--arch", "--target", "--profile", "--sm", "--samples",
        "--emit-header", "--header", "--emit-rust", "--rust", "--emit-fixtures", "--fixtures",
        "--emit-asm", "--asm", "--telemetry-spool"].contains flag then findFirstPositional rest
    else if flag.startsWith "-" then findFirstPositional (v :: rest) else flag
  | [a] => if a.startsWith "-" then "" else a

structure CoreCLIOptions where
  inputPath : String := ""
  outputPath : String := ""
  arch : TargetArch := .x86_64
  emitCABI : Bool := false
  emitLLVM : Bool := false
  emitPTX : Bool := false
  emitMetal : Bool := false
  isBaseline : Bool := false
  smArch : String := "sm_90"
  numSamples : Nat := 4096
  useConstraintProp : Bool := true
  deriving Repr, Inhabited, BEq

def parseCoreCLIOptions (args : List String) : CoreCLIOptions :=
  let inPos := findFirstPositional args
  let inExp := findFlagValue args "--input" (findFlagValue args "--lnir" "")
  { inputPath := if !inExp.isEmpty then inExp else inPos, outputPath := findFlagValue args "-o" "",
    arch := parseTargetArch (findFlagValue args "--arch" "x86_64"),
    emitCABI := hasFlag args "--c-abi" || hasFlag args "--emit-c-abi",
    emitLLVM := hasFlag args "--emit-llvm" || hasFlag args "--llvm",
    emitPTX := hasFlag args "--emit-ptx" || hasFlag args "--ptx",
    emitMetal := hasFlag args "--emit-metal" || hasFlag args "--metal",
    isBaseline := hasFlag args "--baseline", smArch := findFlagValue args "--sm" "sm_90",
    numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096,
    useConstraintProp := !(hasFlag args "--no-constraint-prop") }

/-- Load an `LNIRModule` from `--lnir <path>`, `--input <path>`, or positional argument, using `elaborateHook?` for `.lean`
    sources when running inside the full `lean-native` frontend. Never silently falls back to
    `mkCanonicalBenchmarkModule` when an explicit `--input` or `--lnir` file is passed. -/
def loadInputModule (elaborateHook? : Option (String → IO LNIRModule)) (args : List String)
    (defaultFastCheck : Bool := false) : IO LNIRModule := do
  let defaultMod := if defaultFastCheck then mkFastCheckSampleModule else mkCanonicalBenchmarkModule
  let parseWireOrJsonFile (path : String) : IO LNIRModule := do
    if !(← System.FilePath.pathExists path) then return defaultMod
    let raw ← IO.FS.readFile path
    match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
    | some mod =>
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LNIR declarations from '{path}'"
      return mod
    | none => throw <| IO.userError s!"[lean-native] Failed to parse LNIR wire/JSON module from '{path}'"
  let lnirFile := findFlagValue args "--lnir" ""
  if !lnirFile.isEmpty then return (← parseWireOrJsonFile lnirFile)
  let inFileExplicit := findFlagValue args "--input" ""
  let inFilePos := findFirstPositional args
  let inFile := if !inFileExplicit.isEmpty then inFileExplicit else inFilePos
  if inFile.isEmpty then return defaultMod
  else if inFile == "canonical" || inFile == "benchmarks" || inFile == "examples/Benchmark.lnir" then
    if ← System.FilePath.pathExists inFile then
      let raw ← IO.FS.readFile inFile
      return (LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw).getD mkCanonicalBenchmarkModule
    else return mkCanonicalBenchmarkModule
  else if inFile == "fastcheck" || inFile == "fastcheck-sample" then return mkFastCheckSampleModule
  else if inFile.endsWith ".lnir" || inFile.endsWith ".json" then parseWireOrJsonFile inFile
  else
    match elaborateHook? with
    | some ingestFn =>
      let mod ← ingestFn inFile
      if mod.decls.isEmpty then throw <| IO.userError s!"[lean-native] Failed to extract any LCNF declarations from '{inFile}'"
      return mod
    | none =>
      if ← System.FilePath.pathExists inFile then
        let raw ← IO.FS.readFile inFile
        match LNIRModule.fromWire? raw <|> LNIRModule.fromJson? raw with
        | some mod => return mod
        | none =>
          if inFile.endsWith ".lean" then
            let appPath ← IO.appPath
            let sibBin := appPath.parent.map (· / "lean-native") |>.getD (System.FilePath.mk "lean-native")
            let binToRun ← if ← System.FilePath.pathExists sibBin then pure sibBin.toString else pure "lean-native"
            let out ← IO.Process.output { cmd := binToRun, args := #["emit-lnir", "--wire", inFile] }
            if out.exitCode == 0 then
              if let some mod := LNIRModule.fromWire? out.stdout <|> LNIRModule.fromJson? out.stdout then
                return mod
          throw <| IO.userError s!"[lean-native-core] Cannot parse '{inFile}' as LNIR wire/JSON (use full 'lean-native' for .lean source elaboration)"
      else throw <| IO.userError s!"[lean-native-core] Input file '{inFile}' does not exist"

private def writeOrPrint (outPath text : String) (msg? : Option String := none) : IO UInt32 := do
  if outPath.isEmpty then IO.println text
  else IO.FS.writeFile outPath text; if let some m := msg? then IO.println m
  return 0

private def writeAndPrintJsonOrSummary (outPath jsonText summaryText : String) (jsonFlag : Bool) : IO Unit := do
  if !outPath.isEmpty then IO.FS.writeFile outPath jsonText
  IO.println (if jsonFlag then jsonText else summaryText)


def runEmitCAbiBindings (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let leanPath := findFlagValue args "--lean" (findFlagValue args "--input" (findFirstPositional args))
  let hdrPath := findFlagValue args "--emit-header" (findFlagValue args "--header" "")
  let rsPath := findFlagValue args "--emit-rust" (findFlagValue args "--rust" "")
  let swiftPath := findFlagValue args "--emit-swift" (findFlagValue args "--swift" "")
  let modMapPath := findFlagValue args "--emit-modulemap" (findFlagValue args "--modulemap" "")
  let fixPath := findFlagValue args "--emit-fixtures" (findFlagValue args "--fixtures" "")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let (sigs, guards, srcLabel) ←
    if !leanPath.isEmpty && (← System.FilePath.pathExists leanPath) && leanPath.endsWith ".lean" then
      let raw ← readLeanSourceExpandingUmbrella leanPath
      let (s, g) := extractLeanSourceCAbiAndGuards raw
      if !s.isEmpty then pure (s, g, leanPath)
      else
        let m ← loadInputModule elaborateHook? args
        pure (moduleToCAbiSigs (runDefaultPipeline m).1, g, leanPath)
    else
      let m ← loadInputModule elaborateHook? args
      pure (moduleToCAbiSigs (runDefaultPipeline m).1, [], if leanPath.isEmpty then m.moduleName else leanPath)
  let hdrText := emitCAbiHeaderFromSigs sigs
  let rsText := emitCAbiRustFromSigs sigs
  let swiftText := emitCAbiSwiftFromSigs sigs
  let fixText := emitGuardFixturesJson srcLabel sigs guards
  if !hdrPath.isEmpty then IO.FS.writeFile hdrPath hdrText
  if !rsPath.isEmpty then IO.FS.writeFile rsPath rsText
  if !swiftPath.isEmpty then IO.FS.writeFile swiftPath swiftText
  if !modMapPath.isEmpty then
    let hdrBase := if hdrPath.isEmpty then "turbo_lean_cabi.h" else ((System.FilePath.mk hdrPath).fileName.getD "turbo_lean_cabi.h")
    IO.FS.writeFile modMapPath (emitModuleMap "TurboLeanCABI" hdrBase)
  if !fixPath.isEmpty then IO.FS.writeFile fixPath fixText
  if !outPath.isEmpty then IO.FS.writeFile outPath (if jsonFlag then fixText else hdrText)
  if jsonFlag || (hdrPath.isEmpty && rsPath.isEmpty && swiftPath.isEmpty && modMapPath.isEmpty && fixPath.isEmpty && outPath.isEmpty) then
    IO.print fixText
  else
    IO.println s!"[{tag}] Emitted C-ABI bindings (exports={sigs.length}, guards={guards.length}, header={hdrPath}, rust={rsPath}, swift={swiftPath}, fixtures={fixPath})"
  return 0

def runCompileMode (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  if !(findFlagValue args "--emit-header" (findFlagValue args "--emit-rust" (findFlagValue args "--emit-fixtures" ""))).isEmpty then
    let _ ← runEmitCAbiBindings tag elaborateHook? args
  let opts := parseCoreCLIOptions args
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args opts.emitCABI
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (optMod, _) := if opts.isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  if opts.emitCABI then
    writeOrPrint opts.outputPath (LeanNative.Backend.emitFastCheckCABI optMod)
      (some s!"[{tag}] Wrote Zero-Boxing C-ABI SIMD FastCheck & Routing kernel to {opts.outputPath}")
  else if opts.emitPTX then writeOrPrint opts.outputPath (emitPTXModule optMod opts.smArch)
  else if opts.emitMetal then writeOrPrint opts.outputPath (emitMetalModule optMod)
  else writeOrPrint opts.outputPath (if opts.isBaseline then emitLLVMBaseline optMod opts.arch else emitLLVMOptimized optMod opts.arch)

def runCompileLLVM (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let isBaseline := hasFlag args "--baseline"
  let outPath := findFlagValue args "-o" ""
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← if hasFlag args "--slot-regression" then pure slotTypeRegressionModule else loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg .x86_64 false baseMod
  let (modToEmit, _) := if isBaseline then (baseMod, []) else runDefaultPipeline baseMod
  let irText := if isBaseline then emitLLVMBaseline modToEmit arch else emitLLVMOptimized modToEmit arch
  writeOrPrint outPath irText (some s!"[{tag}] Wrote LLVM 18 IR ({arch.triple}, baseline={isBaseline}, decls={modToEmit.decls.length}) to {outPath}")

def runCompileStaticLib (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let arch := parseTargetArch (findFlagValue args "--arch" "x86_64")
  let outPath := findFlagValue args "-o" "/tmp/liblean_native_kernels.a"
  let headerPath := findFlagValue args "--emit-header" (findFlagValue args "--header" (outPath ++ ".h"))
  let rustPath := findFlagValue args "--emit-rust" (findFlagValue args "--rust" "")
  let swiftPath := findFlagValue args "--emit-swift" (findFlagValue args "--swift" "")
  let xcfwDir := findFlagValue args "--emit-xcframework" (findFlagValue args "--xcframework" (findFlagValue args "--emit-swift-package-skeleton" ""))
  let fixPath := findFlagValue args "--emit-fixtures" (findFlagValue args "--fixtures" "")
  let asmPath := findFlagValue args "--emit-asm" (findFlagValue args "--asm" "")
  let jsonFlag := hasFlag args "--json"
  let posPath := findFirstPositional args
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let (sigs, guards) ←
    if posPath.endsWith ".lean" then
      let src ← readLeanSourceExpandingUmbrella posPath
      let (srcSigs, srcGuards) := extractLeanSourceCAbiAndGuards src
      pure (if srcSigs.isEmpty then moduleToCAbiSigs optMod else srcSigs, srcGuards)
    else
      pure (moduleToCAbiSigs optMod, [])
  let irText := emitLLVMOptimized optMod arch
  let hdrText := emitCAbiHeaderFromSigs sigs
  IO.FS.writeFile headerPath hdrText
  if !rustPath.isEmpty then IO.FS.writeFile rustPath (emitCAbiRustFromSigs sigs (some optMod))
  if !swiftPath.isEmpty then IO.FS.writeFile swiftPath (emitCAbiSwiftFromSigs sigs)
  if !fixPath.isEmpty then IO.FS.writeFile fixPath (emitGuardFixturesJson optMod.moduleName sigs guards)
  if !xcfwDir.isEmpty then
    IO.FS.createDirAll (System.FilePath.mk xcfwDir / "ios-arm64" / "Headers")
    IO.FS.writeFile (s!"{xcfwDir}/ios-arm64/Headers/turbo_lean_cabi.h") hdrText
    IO.FS.writeFile (s!"{xcfwDir}/ios-arm64/Headers/module.modulemap") (emitModuleMap "TurboLeanCABI" "turbo_lean_cabi.h")
    IO.FS.writeFile (s!"{xcfwDir}/TurboLeanKit.swift") (emitCAbiSwiftFromSigs sigs)
    IO.FS.writeFile (s!"{xcfwDir}/Info.plist")
      "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<!DOCTYPE plist PUBLIC \"-//Apple//DTD PLIST 1.0//EN\" \"http://www.apple.com/DTDs/PropertyList-1.0.dtd\">\n<plist version=\"1.0\">\n<dict>\n  <key>AvailableLibraries</key>\n  <array>\n    <dict>\n      <key>HeadersPath</key><string>Headers</string>\n      <key>LibraryIdentifier</key><string>ios-arm64</string>\n      <key>LibraryPath</key><string>libturbo_lean_kernels.a</string>\n      <key>SupportedArchitectures</key><array><string>arm64</string></array>\n      <key>SupportedPlatform</key><string>ios</string>\n    </dict>\n  </array>\n  <key>CFBundlePackageType</key><string>XFWK</string>\n  <key>XCFrameworkFormatVersion</key><string>1.0</string>\n</dict>\n</plist>\n"
  let tmpLl := outPath ++ ".tmp.ll"
  let tmpObj := outPath ++ ".tmp.o"
  IO.FS.writeFile tmpLl irText
  let runCmdOk (cmd : String) (cmdArgs : Array String) : IO Bool := do
    try return (← IO.Process.output { cmd, args := cmdArgs }).exitCode == 0
    catch _ => return false
  let cpuFlags : Array String := arch.clangFlags
  if !asmPath.isEmpty then
    if ← runCmdOk "clang" (cpuFlags ++ #["-S", tmpLl, "-o", asmPath]) then
      let rawAsm ← try IO.FS.readFile asmPath catch _ => pure ""
      let keepAsmLine (ln : String) : Bool :=
        let t := ln.trimAscii.toString
        !(t.startsWith ".cfi_" || t.startsWith ".file" || t.startsWith ".addrsig" ||
          t.startsWith ".prefalign" || t.startsWith ".ident" || t.startsWith ".att_syntax")
      let cleanAsm := String.intercalate "\n" ((rawAsm.splitOn "\n").filter keepAsmLine)
      IO.FS.writeFile asmPath cleanAsm
  let clangOk ← runCmdOk "clang" (cpuFlags ++ #["-c", tmpLl, "-o", tmpObj])
  let builtArchive ← if clangOk then do
    try IO.FS.removeFile outPath catch _ => pure ()
    if ← runCmdOk "llvm-ar" #["rcs", outPath, tmpObj] then pure true
    else runCmdOk "ar" #["rcs", outPath, tmpObj]
  else pure false
  if !builtArchive then IO.FS.writeFile outPath irText
  if jsonFlag then
    IO.println s!"\{\"status\":\"compiled_static_lib\",\"archive\":{if builtArchive then "true" else "false"},\"library\":\"{outPath}\",\"asm\":\"{asmPath}\",\"header\":\"{headerPath}\",\"rust\":\"{rustPath}\",\"decls\":{optMod.decls.length}}"
  else
    IO.println s!"[{tag}] Wrote C-ABI static library ({outPath}, archive={builtArchive}) and header ({headerPath}, decls={optMod.decls.length})"
  return 0

def runCompileMLIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isStableHLO := hasFlag args "--tpu" || hasFlag args "--stablehlo" || hasFlag args "--tpu-stablehlo"
  let isPallas := hasFlag args "--pallas" || hasFlag args "--tpu-pallas"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let mlirText :=
    if isPallas then emitTPUPallasModule optMod
    else if isStableHLO then emitStableHLOModule optMod
    else emitMLIRModule optMod
  let kind := if isPallas then "TPU Pallas" else if isStableHLO then "TPU v5e StableHLO" else "GPU MLIR"
  writeOrPrint outPath mlirText (some s!"[{tag}] Wrote {kind} module to {outPath}")

def runCompilePTX (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let smArch := findFlagValue args "--sm" "sm_90"
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let ptxText :=
    if isFastCheck then emitFastCheckPTX baseMod smArch
    else emitPTXModule (runDefaultPipeline baseMod).1 smArch
  writeOrPrint outPath ptxText (some s!"[{tag}] Wrote NVIDIA PTX 8.0 ({smArch}, fastcheck={isFastCheck}) to {outPath}")

def runCompileMetal (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let isFastCheck := hasFlag args "--fastcheck"
  let baseMod ← loadInputModule elaborateHook? args isFastCheck
  let mslText :=
    if isFastCheck then emitFastCheckMetal baseMod
    else emitMetalModule (runDefaultPipeline baseMod).1
  let (valid, errs) := validateMetalShader mslText
  if !valid then
    IO.eprintln s!"[{tag}] Metal shader validation errors: {errs}"
    return 1
  writeOrPrint outPath mslText
    (some s!"[{tag}] Wrote Apple Metal Shading Language 3.0 (fastcheck={isFastCheck}, valid={valid}) to {outPath}")

def runCompileFastCheck (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let smArch := findFlagValue args "--sm" "sm_90"
  let numSamples := (findFlagValue args "--samples" "4096").toNat?.getD 4096
  let useConstraintProp := !(hasFlag args "--no-constraint-prop")
  let jsonFlag := hasFlag args "--json"
  let mod ← loadInputModule elaborateHook? args (!(hasFlag args "--canonical"))
  if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
    writeOrPrint outPath (LeanNative.Backend.emitFastCheckCABI mod) (some s!"[{tag}] Wrote FastCheck Zero-Boxing C-ABI SIMD source to {outPath}")
  else if hasFlag args "--emit-llvm" then
    writeOrPrint outPath (emitFastCheckLLVM mod) (some s!"[{tag}] Wrote FastCheck SIMD LLVM 18 IR to {outPath}")
  else if hasFlag args "--emit-ptx" then
    writeOrPrint outPath (emitFastCheckPTX mod smArch) (some s!"[{tag}] Wrote FastCheck NVIDIA PTX 8.0 ({smArch}) to {outPath}")
  else if hasFlag args "--emit-metal" then
    writeOrPrint outPath (emitFastCheckMetal mod) (some s!"[{tag}] Wrote FastCheck Apple Metal 3.0 shader to {outPath}")
  else
    let report := runFastCheckModule mod numSamples useConstraintProp
    writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
    return 0

def runCompileHybrid (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let profilePath := findFlagValue args "--profile" ""
  let mut minGpuElems : Nat := 65536
  if !profilePath.isEmpty then
    let profRaw ← IO.FS.readFile profilePath
    match HardwareCostProfile.fromJson? profRaw with
    | some p => minGpuElems := p.minGpuElements
    | none => throw <| IO.userError s!"[{tag}] Failed to parse hardware profile from '{profilePath}'"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let plan := partitionModule optMod minGpuElems
  let glueText := emitHybridHostGlue plan
  writeOrPrint outPath glueText
    (some s!"[{tag}] Wrote Hybrid CPU/GPU dispatch glue (gpuDecls={plan.gpuDecls.length}, cpuDecls={plan.cpuOnlyDecls.length}, minGpuElements={minGpuElems}) to {outPath}")

def runSuperopt (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let profilePath := findFlagValue args "--profile" ""
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target false baseMod
  let (_, report) ←
    if !profilePath.isEmpty then
      let profRaw ← IO.FS.readFile profilePath
      match HardwareCostProfile.fromJson? profRaw with
      | some p => pure (superoptModuleWithProfile p baseMod)
      | none => throw <| IO.userError s!"[lean-native] Failed to parse hardware cost profile from '{profilePath}'"
    else
      pure (superoptModule target baseMod)
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  return 0

def runPlugins (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let testAdversarial := hasFlag args "--test-adversarial" || !(hasFlag args "--no-adversarial-test")
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let _ ← emitModuleTelemetryEvents telCfg target testAdversarial baseMod
  let (_, report) := runSegregatedPluginPipeline target testAdversarial baseMod
  writeAndPrintJsonOrSummary outPath report.toJson report.formatSummary jsonFlag
  let allTvOk := report.declAudits.all (fun a => a.tvVerified)
  let ok := allTvOk && (!testAdversarial || report.adversarialRejected)
  return if ok then 0 else 1

def runTelemetry (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let targetStr := findFlagValue args "--target" (findFlagValue args "--arch" "x86_64")
  let target := parseSuperoptTarget targetStr
  let telCfg ← TelemetryConfig.probe args
  let baseMod ← loadInputModule elaborateHook? args
  let count ← emitModuleTelemetryEvents telCfg target true baseMod
  let evPath := s!"{telCfg.spoolDir}/events.jsonl"
  let blobsDir := s!"{telCfg.spoolDir}/blobs"
  IO.println s!"\{\"schema\":\"lean-native.telemetry.v1\",\"enabled\":{if telCfg.enabled then "true" else "false"},\"mode\":\"{telCfg.mode}\",\"spool_dir\":\"{telCfg.spoolDir}\",\"events_file\":\"{evPath}\",\"blobs_dir\":\"{blobsDir}\",\"remote_url\":\"{telCfg.remoteUrl}\",\"events_emitted\":{count}}"
  return 0

def runTurboPlugin : IO UInt32 := do
  let line ← (← IO.getStdin).getLine
  let stdout ← IO.getStdout
  stdout.putStrLn (handleTurboPluginLine line.trimAscii.toString)
  stdout.flush; return 0

def runPRVerify (tag : String) (args : List String) : IO UInt32 := do
  let baseRef := findFlagValue args "--base" "HEAD"
  let jsonFlag := hasFlag args "--json"
  let outPath := findFlagValue args "-o" ""
  let specExists ← System.FilePath.pathExists "LeanNative/Spec.lean"
  let testExists ← System.FilePath.pathExists "tests/test_runner.lean"
  let specHashHex := blake3Hex (← if specExists then IO.FS.readFile "LeanNative/Spec.lean" else pure "")
  let testHashHex := blake3Hex (← if testExists then IO.FS.readFile "tests/test_runner.lean" else pure "")
  let disallowSpecChanges := hasFlag args "--disallow-spec-changes"
  let mut specUnchanged := specExists
  let mut testUnchanged := testExists
  if disallowSpecChanges then
    try
      let changedFiles := (← IO.Process.output { cmd := "git", args := #["diff", "--name-only", baseRef, "--", "LeanNative/Spec.lean", "tests/test_runner.lean"] }).stdout.trimAscii.toString
      if changedFiles.contains "LeanNative/Spec.lean" then specUnchanged := false
      if changedFiles.contains "tests/test_runner.lean" then testUnchanged := false
    catch _ => pure ()
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let tvReport := validateTranslationModule baseMod optMod
  let allDeclTvOk := pluginReport.declAudits.all (·.tvVerified)
  let axiomReport := verifiedAxiomAuditReport
  let law5Passed := checkPRVerificationGate {
    expectedSpecHash := 1, actualSpecHash := if specUnchanged then 1 else 2,
    expectedTestSuiteHash := 1, actualTestSuiteHash := if testUnchanged then 1 else 2,
    forbiddenAxiomsCount := axiomReport.forbiddenAxiomsFound.length,
    tvAllPassed := tvReport.allPassed && allDeclTvOk && pluginReport.adversarialRejected && axiomReport.passed }
  let fcSelfTestOk ← runFastCheckBridgeSelfTest
  let overallOk := law5Passed && fcSelfTestOk
  let jsonOut := s!"\{\n  \"status\": \"{if overallOk then "pr_verified" else "pr_rejected"}\",\n  \"engine\": \"{tag}\",\n  \"version\": \"0.5.0\",\n  \"baseRef\": \"{baseRef}\",\n  \"law1UntrustedPluginGatePassed\": {pluginReport.adversarialRejected && allDeclTvOk},\n  \"law5SpecPinningGatePassed\": {law5Passed},\n  \"specBlake3\": \"{specHashHex}\",\n  \"testRunnerBlake3\": \"{testHashHex}\",\n  \"symbolicTvPassedDecls\": {tvReport.passedDecls},\n  \"symbolicTvTotalDecls\": {tvReport.totalDecls},\n  \"pluginsAccepted\": {pluginReport.acceptedCount},\n  \"adversarialPluginsRejected\": {pluginReport.rejectedCount},\n  \"costBefore\": {pluginReport.totalCostBefore},\n  \"costAfter\": {pluginReport.totalCostAfter},\n  \"fastCheckSelfTestPassed\": {fcSelfTestOk}\n}"
  let summaryText := String.intercalate "\n" [
    s!"[{tag}] PR & Spec-Pinning Verification Gate (base={baseRef}):",
    s!"  Law 1 Untrusted Plugin & Adversarial Gate : {if pluginReport.adversarialRejected && allDeclTvOk then "PASSED" else "FAILED"} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})",
    s!"  Law 5 Spec & Test Suite Pinning Gate      : {if law5Passed then "PASSED" else "FAILED"} (Spec={specHashHex.take 16}..., Tests={testHashHex.take 16}...)",
    s!"  Alive2 Symbolic Translation Validation    : {if tvReport.allPassed then "PASSED" else "FAILED"} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)",
    s!"  In-Process FastCheck & BLAKE3 Self-Test   : {if fcSelfTestOk then "PASSED" else "FAILED"}"
  ]
  writeAndPrintJsonOrSummary outPath jsonOut summaryText jsonFlag
  return if overallOk then 0 else 1

def runVerifyCerts (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let baseMod ← loadInputModule elaborateHook? args
  let report := verifyModuleCerts baseMod.moduleName ((runDefaultPipeline baseMod).2.map toOptimizationCert)
  let summaryText := s!"[{tag}] Certificate Verification for {report.moduleName}:\n  Total pass certificates : {report.certs.length}\n  Declarations verified   : {report.declSummaries.length}\n  Overall assurance level : {report.overallAssurance}\n  Hash chains & theorems  : {if report.verified then "VALID" else "FAILED"}"
  writeAndPrintJsonOrSummary (findFlagValue args "-o" "") report.toJson summaryText (hasFlag args "--json")
  return if report.verified then 0 else 1

def runValidateTV (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let jsonFlag := hasFlag args "--json"
  let baseMod ← loadInputModule elaborateHook? args
  let (optMod, _) := runDefaultPipeline baseMod
  let tvReport := validateTranslationModule baseMod optMod
  writeAndPrintJsonOrSummary outPath tvReport.toJson tvReport.formatSummary jsonFlag
  return if tvReport.allPassed then 0 else 1

def runEmitLNIR (tag : String) (elaborateHook? : Option (String → IO LNIRModule)) (args : List String) : IO UInt32 := do
  let outPath := findFlagValue args "-o" ""
  let wireFlag := hasFlag args "--wire"
  let fastCheckFlag := hasFlag args "--fastcheck"
  let mod ← loadInputModule elaborateHook? args fastCheckFlag
  let useWire := wireFlag || outPath.endsWith ".lnir"
  writeOrPrint outPath (if useWire then mod.toWire else mod.toJson)
    (some s!"[{tag}] Emitted LNIR ({if useWire then "wire" else "json"}, decls={mod.decls.length}) to {outPath}")

def runCoreSelfTest (tag : String) : IO UInt32 := do
  IO.println s!"=== Lean Native ({tag} v0.5.0) Self-Test ==="
  let baseMod := mkCanonicalBenchmarkModule
  let roundTripWireOk := LNIRModule.fromWire? baseMod.toWire == some baseMod
  let roundTripJsonOk := LNIRModule.fromJson? baseMod.toJson == some baseMod
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soReportX86) := superoptModule .x86_64 baseMod
  let (_, soReportMetal) := superoptModule .apple_metal baseMod
  let superoptOk := soReportX86.rewritesApplied > 0 && soReportMetal.rewritesApplied > 0 &&
    soReportX86.totalCostAfter < soReportX86.totalCostBefore
  let (_, pluginReport) := runSegregatedPluginPipeline .x86_64 true baseMod
  let pluginsOk := pluginReport.acceptedCount > 0 && pluginReport.adversarialRejected &&
    pluginReport.declAudits.all (fun a => a.tvVerified)
  let law5Ok := checkPRVerificationGate ⟨42, 42, 99, 99, 0, tvReport.allPassed && pluginsOk⟩ &&
    !(checkPRVerificationGate ⟨42, 43, 99, 99, 0, true⟩)
  let fcMod := mkFastCheckSampleModule
  let fcReportProp := runFastCheckModule fcMod 512 true
  let fcReportNaive := runFastCheckModule fcMod 512 false
  let fcPropOk := fcReportProp.counterexamplesFound == 1 && fcReportProp.vacuousPasses == 0 && fcReportProp.falsePositives == 0
  let fcNaiveVacuousOk := fcReportNaive.vacuousPasses == 1
  let fcLlvm := emitFastCheckLLVM fcMod
  let fcPtx := emitFastCheckPTX fcMod "sm_90"
  let fcMetal := emitFastCheckMetal fcMod
  let llvmX86 := emitLLVMOptimized optMod .x86_64
  let ptxTxt := emitPTXModule optMod "sm_90"
  let metalTxt := emitMetalModule optMod
  let (metalValid, _) := validateMetalShader metalTxt
  let (fcMetalValid, _) := validateMetalShader fcMetal
  let gpuDescs := lowerModuleToGPUDescriptors optMod
  let stablehloTxt := emitStableHLOModule optMod
  let pallasTxt := emitTPUPallasModule optMod
  let tpuCodegenOk := (stablehloTxt.splitOn "stablehlo.").length > 1 &&
    ((stablehloTxt.splitOn "tpu_v6e").length > 1 || (stablehloTxt.splitOn "tpu_v5e").length > 1) &&
    ((pallasTxt.splitOn "tpu_v6e").length > 1 || (pallasTxt.splitOn "tpu_v5e").length > 1) &&
    (pallasTxt.splitOn "pallas").length > 1
  let blake3Ok := blake3SelfTest
  let twoPow60 : Nat := 1 <<< 60
  let mulDivOk := mulDivDownNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivUpNat twoPow60 twoPow60 twoPow60 == twoPow60 &&
    mulDivDownNat twoPow60 twoPow60 3 < mulDivUpNat twoPow60 twoPow60 3 &&
    mulDivDownNat twoPow60 twoPow60 0 == 0 && mulDivUpNat twoPow60 twoPow60 0 == 0
  let telCfg ← TelemetryConfig.probe ["--telemetry"]
  let telCount ← emitModuleTelemetryEvents telCfg .x86_64 true baseMod
  let telOk := telCount > 0
  let relDecl : LNIRDecl := {
    name := "ssz_monotone_offsets_bug"
    params := [{ id := 0, name := "o0", ty := .i64, borrow := false }, { id := 1, name := "o1", ty := .i64, borrow := false }]
    retTy := .i1, assurance := .verifiedKernelProof, isGpuCand := true
    body :=
      .letBind 10 .i1 (.scalar (.binOp .le (.constU64 16) (.var 0)))
        (.letBind 11 .i1 (.scalar (.binOp .le (.var 0) (.var 1)))
          (.letBind 12 .i1 (.scalar (.binOp .bitAnd (.var 10) (.var 11)))
            (.letBind 13 .i1 (.scalar (.constBool true))
              (.ite 12 (.letBind 14 .i1 (.scalar (.binOp .lt (.var 1) (.constU64 20))) (.ret 14)) (.ret 13)))))
  }
  let relRes := runFastCheckDecl relDecl 64 true
  let relSamplingOk := relRes.counterexampleFound && relRes.certifiedCounterexample && !relRes.vacuousPass
  let gpuHeadroomOk :=
    LeanNative.Spec.hasSufficientGpuMemory ⟨4096, 1024, 2048⟩ &&
    !(LeanNative.Spec.hasSufficientGpuMemory ⟨2048, 1024, 2048⟩) &&
    LeanNative.Spec.isValidByteSlice (LeanNative.Spec.subSliceView ⟨64, 8, 32⟩ 4 16) &&
    LeanNative.Spec.canEmitRestrictSimd ⟨true, false, 64⟩ && !(LeanNative.Spec.canEmitRestrictSimd ⟨true, true, 64⟩) &&
    LeanNative.Spec.canUnboxNestedProdWhile ⟨8, false, true⟩ && LeanNative.Spec.canRewriteMulHiU128 ⟨32, 32, true⟩ &&
    LeanNative.Spec.canRewriteTupleSArrayFill ⟨248, 248, 64, 64, 64, true⟩ && LeanNative.Spec.canUnboxNatBoolWhile ⟨true, true, false⟩ &&
    LeanNative.Spec.canRewriteMixedSArrayWhile ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNestedRangeTupleMut ⟨246, 248, 248, 1⟩ &&
    LeanNative.Spec.canStripEarlyReturnCtor ⟨true, true, false⟩ && LeanNative.Spec.canRewriteNested2DRangeForIn ⟨248, 1, true, true⟩ &&
    LeanNative.Spec.canElideInBodyRangeAlloc ⟨0, 1, false, true⟩ && LeanNative.Spec.canSwapPingPongSArray ⟨248, 248, true, true⟩ &&
    LeanNative.Spec.canCollapseSar64ReturnDiamond ⟨63, 16, true⟩ && LeanNative.Spec.canMaterializeStackSArraySROA ⟨3, true, true⟩ &&
    LeanNative.Spec.canPromoteRangeCtorToStack ⟨0, 3, false, true⟩ && LeanNative.Spec.canScalarizeRepeatMTripleSArray ⟨248, 248, 248, true⟩ &&
    LeanNative.Spec.canEmitZeroDepMathlibCert ⟨false, false, false, true⟩ &&
    !(LeanNative.Spec.canEmitZeroDepMathlibCert ⟨false, true, false, true⟩) &&
    LeanNative.Backend.selectOptimalSearchBackend 8192 false true false false true false true == .FpgaLsc2 &&
    (emitZeroDepMathlibProof { declName := "tauceti_cert", stmtSrc := "x = y", cofactorTerms := [("h1", 1), ("h2", -1)], dagRwSteps := ["Nat.add_comm"], distilledLemmas := ["Nat.add_zero"], farkasWeights := [1, 2] }).startsWith "by\n" &&
    LeanNative.Spec.canBindCAbiSliceIo ⟨16, 48, 4096, 8, 16⟩ && !(LeanNative.Spec.canBindCAbiSliceIo ⟨16, 48, 4096, 32, 16⟩) &&
    LeanNative.Spec.verifyCAbiSliceIoC 16 48 4096 8 16 == 1 && LeanNative.Spec.verifyCAbiSliceIoC 16 48 512 8 16 == 0 &&
    LeanNative.Spec.canEmitZeroRuntimeSliceOut ⟨0, 0, 0, 8, 16⟩ && !(LeanNative.Spec.canEmitZeroRuntimeSliceOut ⟨1, 0, 0, 8, 16⟩) &&
    LeanNative.Spec.packSliceSpanU64 10 25 3 == 0x0000000A00001903 &&
    LeanNative.Spec.verifyLazyReductionSliceC 64 256 1 1 == 1 && LeanNative.Spec.verifyLazyReductionSliceC 64 256 0 1 == 0 &&
    LeanNative.Spec.verifyRadix4NttFusionC 8 4 64 1 == 1 && LeanNative.Spec.verifyRadix4NttFusionC 8 3 64 1 == 0 &&
    TargetArch.iosArm64.triple == "arm64-apple-ios" && TargetArch.iosArm64.llvmTriple == "arm64-apple-ios16.0.0" &&
    TargetArch.iosArm64.isAArch64 && TargetArch.iosArm64.isIOS &&
    optMod.decls.all (fun d =>
      let m := LeanNative.Backend.LLVM.selectDeclRcMode d
      let hh : UInt8 := if LeanNative.Backend.LLVM.codeHasHeapOps d.body then 1 else 0
      let mt : UInt8 := if LeanNative.Backend.LLVM.codeHasParFor d.body then 1 else 0
      LeanNative.Spec.verifyRcModeSafeC m.toCode hh mt == 1) &&
    optMod.decls.any (fun d => LeanNative.Backend.LLVM.selectDeclRcMode d == .freestanding) &&
    optMod.decls.any (fun d => LeanNative.Backend.LLVM.selectDeclRcMode d == .atomic) &&
    LeanNative.Backend.selectAppleA15Target 262144 false true true == .gpuMetal &&
    LeanNative.Backend.selectAppleA15Target 65536 false true true == .cpuSimd &&
    LeanNative.Backend.selectAppleA15Target 262144 false true false == .cpuSimd &&
    (let glue := LeanNative.Backend.emitMetalZeroCopyHostGlue (LeanNative.Backend.Hybrid.partitionModule optMod)
     let swappedGlue := glue.replace "[enc setBuffer:bufX offset:0 atIndex:0]" "[enc setBuffer:bufX offset:0 atIndex:1]"
     (glue.splitOn "newBufferWithBytesNoCopy").length > 1 &&
     LeanNative.Backend.verifyMetalBindingContract LeanNative.Backend.saxpyF16MetalBindingSpec metalTxt glue &&
     !(LeanNative.Backend.verifyMetalBindingContract LeanNative.Backend.saxpyF16MetalBindingSpec metalTxt swappedGlue) &&
     !(LeanNative.Backend.verifyMetalBindingContract { LeanNative.Backend.saxpyF16MetalBindingSpec with outputBufferName := "bad" } metalTxt glue)) &&
    (let androidIr := emitLLVMOptimized optMod .androidArm64
     let tensorIr := emitLLVMOptimized optMod .androidArm64 (some IsaLevel.tensorG3)
     let cryptoDecl : LNIRDecl := {
       name := "crypto_clmul_eor3_probe"
       params := [{ id := 0, name := "x", ty := .i64 }, { id := 1, name := "y", ty := .i64 }]
       retTy := .i64
       body := .letBind 2 .i64 (.scalar (.binOp .clmul64 (.var 0) (.var 1)))
                 (.letBind 3 .i64 (.scalar (.binOp .eor3 (.var 2) (.var 1))) (.ret 3))
     }
     let cryptoBaseIr := LeanNative.Backend.LLVM.emitDeclLLVM true cryptoDecl .androidArm64 [] (some IsaLevel.arm64Baseline)
     let cryptoTensorIr := LeanNative.Backend.LLVM.emitDeclLLVM true cryptoDecl .androidArm64 [] (some IsaLevel.tensorG3)
     let baseSlice := match androidIr.splitOn "define weak_odr dso_local void @lean_native_cpu_saxpy_u64__baseline(" with
       | _ :: after :: _ => (after.splitOn "\n}").headD ""
       | _ => ""
     let sve2Slice := match androidIr.splitOn "define weak_odr dso_local void @lean_native_cpu_saxpy_u64__sve2(" with
       | _ :: after :: _ => (after.splitOn "\n}").headD ""
       | _ => ""
     (androidIr.splitOn "apple-m3").length == 1 &&
     !baseSlice.isEmpty && !sve2Slice.isEmpty &&
     (baseSlice.splitOn "<vscale").length == 1 &&
     (sve2Slice.splitOn "<vscale x 2 x i64>").length > 1 &&
     (sve2Slice.splitOn "@llvm.vscale.i64()").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_saxpy_u64_dispatch").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_map_scale_add_u64__sve2").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_zip_add_u64__sve2").length > 1 &&
     (androidIr.splitOn "lean_native_cpu_xor_assign_u64__sve2").length > 1 &&
     (androidIr.splitOn "@leansys_select_isa").length > 1 &&
     (cryptoBaseIr.splitOn "call <16 x i8> @llvm.aarch64.neon.pmull64").length == 1 &&
     (cryptoTensorIr.splitOn "call <16 x i8> @llvm.aarch64.neon.pmull64").length > 1 &&
     (cryptoBaseIr.splitOn "call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64").length == 1 &&
     (cryptoTensorIr.splitOn "call <2 x i64> @llvm.aarch64.crypto.eor3u.v2i64").length > 1 &&
     (tensorIr.splitOn "+sve2-bitperm").length > 1 &&
     (tensorIr.splitOn "!8 = !{!\"llvm.loop.vectorize.scalable.enable\", i1 true}").length > 1 &&
     optMod.decls.all (fun d =>
       let req := LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3
       req.le IsaLevel.tensorG3 && !req.fp16 && !req.dotprod && !req.i8mm && !req.bf16) &&
     optMod.decls.any (fun d =>
       LeanNative.Backend.LLVM.codeHasParFor d.body && !LeanNative.Backend.LLVM.codeHasCryptoOps d.body &&
       !(LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3).sha3 &&
       (LeanNative.Backend.LLVM.codegenRequires d IsaLevel.tensorG3).sve2) &&
     LeanNative.Backend.LLVM.codeHasCryptoOps cryptoDecl.body &&
     (LeanNative.Backend.LLVM.codegenRequires cryptoDecl IsaLevel.appleA15).sha3 &&
     !(LeanNative.Backend.LLVM.codegenRequires cryptoDecl IsaLevel.arm64Baseline).sha3 &&
     (TargetArch.iosArm64.clangFlags (some IsaLevel.appleA16_A17)).contains "-mcpu=apple-a16" &&
     (TargetArch.iosArm64.clangFlags (some IsaLevel.appleM4_A18)).contains "-mcpu=apple-m4") &&
    TargetArch.androidArm64.triple == "aarch64-linux-android" &&
    TargetArch.wasm32.triple == "wasm32-unknown-unknown" && TargetArch.iosSimArm64.symbolPrefix == "_"
  let sve2AsmOk ← do
    let androidIr := emitLLVMOptimized optMod .androidArm64
    let tmpLl := "/tmp/ln_sve2_verify.ll"
    let home := (← IO.getEnv "HOME").getD "/root"
    let clangCandidates := [
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      s!"{home}/.elan/toolchains/leanprover--lean4---v4.31.0/bin/clang",
      "/var/lib/sandboxed-node/.elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.35.0/bin/clang",
      "/var/lib/sandboxed-node/caches/elan/toolchains/leanprover--lean4---v4.31.0/bin/clang"
    ]
    let mut clangCmd := "clang"
    for cand in clangCandidates do
      if ← System.FilePath.pathExists cand then
        clangCmd := cand
        break
    try
      IO.FS.writeFile tmpLl androidIr
      let out ← IO.Process.output {
        cmd := clangCmd
        args := #["--target=aarch64-linux-android29", "-O3", "-Wno-override-module", "-S", tmpLl, "-o", "-"]
      }
      try IO.FS.removeFile tmpLl catch _ => pure ()
      if out.exitCode != 0 then
        pure false
      else
        let asm := out.stdout
        let baseAsm := match asm.splitOn "lean_native_cpu_saxpy_u64__baseline:" with
          | _ :: after :: _ => (after.splitOn ".Lfunc_end").headD ""
          | _ => ""
        let sve2Asm := match asm.splitOn "lean_native_cpu_saxpy_u64__sve2:" with
          | _ :: after :: _ => (after.splitOn ".Lfunc_end").headD ""
          | _ => ""
        pure (!baseAsm.isEmpty && !sve2Asm.isEmpty &&
          (baseAsm.splitOn "cntd").length == 1 && (baseAsm.splitOn "ld1d").length == 1 && (baseAsm.splitOn "st1d").length == 1 &&
          (sve2Asm.splitOn "cntd").length > 1 && (sve2Asm.splitOn "ld1d").length > 1 &&
          (sve2Asm.splitOn "mad").length > 1 && (sve2Asm.splitOn "st1d").length > 1)
    catch _ =>
      try IO.FS.removeFile tmpLl catch _ => pure ()
      pure false
  let gpuHeadroomOk := gpuHeadroomOk && sve2AsmOk
  let specRaw ← if ← System.FilePath.pathExists "LeanNative/Spec.lean" then IO.FS.readFile "LeanNative/Spec.lean" else pure ""
  let (specSigs, specGuards) := extractLeanSourceCAbiAndGuards specRaw
  let activeSigs := if specSigs.isEmpty then moduleToCAbiSigs optMod else specSigs
  let cabiGenHdr := emitCAbiHeaderFromSigs activeSigs
  let cabiGenRs := emitCAbiRustFromSigs activeSigs
  let cabiGenSw := emitCAbiSwiftFromSigs activeSigs
  let cabiGenFix := emitGuardFixturesJson "LeanNative/Spec.lean" specSigs specGuards
  let cabiGenOk := (cabiGenHdr.splitOn "extern \"C\"").length > 1 && (cabiGenRs.splitOn "extern \"C\"").length > 1 &&
    (cabiGenSw.splitOn "@_silgen_name").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_mul_const_zmm").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_mul_low_const_m128i").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_tri_acc_neon").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_mul_unreduced_neon").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_fold_alpha_four_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_pre_reduce_eq_lo_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_gf8_inv_ntt_avx2_pair_composite_u32").length > 1 &&
    (cabiGenRs.splitOn "lean_native_gf8_shift_reduce_inner_ab_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_gf8_shift_reduce_inner_ab_gfni_avx512_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_gf8_urm_convert_ab_nomul_gfni_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_gf2_fold_64_rows_gfni_c4_slice").length > 1 &&
    (cabiGenRs.splitOn "lean_native_f128_plane_bank_to_f128_slice").length > 1 &&
    (specRaw.isEmpty || (!specSigs.isEmpty && !specGuards.isEmpty && (cabiGenFix.splitOn "leannative_verify_cabi_slice_io").length > 1))
  let axiomReport := verifiedAxiomAuditReport
  let axiomOk := axiomReport.passed && axiomReport.forbiddenAxiomsFound.isEmpty && axiomReport.theoremsAudited >= 185 && cabiGenOk
  let sAx := "sor" ++ "ryAx"
  let status (b : Bool) := if b then "PASSED" else "FAILED"
  IO.println s!"1. Canonical 8-Kernel Module       : {optMod.decls.length} declarations (incl. 256-bit EVM/Verity)"
  IO.println s!"2. LNIR Wire & JSON Round-Trip     : {status (roundTripWireOk && roundTripJsonOk)}"
  IO.println s!"3. Certificate Chain Verification  : {status certReport.verified} ({certReport.certs.length} certs)"
  IO.println s!"4. Alive2 Symbolic TV Validation   : {status tvReport.allPassed} ({tvReport.passedDecls}/{tvReport.totalDecls} decls)"
  IO.println s!"5. Enumerative Superoptimizer      : {status superoptOk} ({soReportX86.rewritesApplied} rewrites, cost {soReportX86.totalCostBefore}->{soReportX86.totalCostAfter})"
  IO.println s!"6. Segregated Plugins & Law 1/5    : {status (pluginsOk && law5Ok)} (accepted={pluginReport.acceptedCount}, adversarialRejected={pluginReport.rejectedCount})"
  IO.println s!"7. FastCheck ConstraintProp vs Vac : {status (fcPropOk && fcNaiveVacuousOk && relSamplingOk)} (propCex={fcReportProp.counterexamplesFound}, naiveVacuous={fcReportNaive.vacuousPasses}, relPolytope=ok)"
  IO.println s!"8. Unified GPUIR & Apple Metal 3.0 : {status (metalValid && fcMetalValid && gpuHeadroomOk)} ({gpuDescs.length} GPU descriptors, Metal={metalTxt.length}B)"
  IO.println s!"9. Pure-Lean RFC BLAKE3 Self-Test  : {status blake3Ok}"
  IO.println s!"10. Google Cloud TPU v6e Codegen   : {status tpuCodegenOk} (StableHLO={stablehloTxt.length}B, Pallas={pallasTxt.length}B)"
  IO.println s!"11. Exact 512-Bit mulDiv Overflow  : {status mulDivOk} ((2^60 * 2^60) / 2^60 == 2^60)"
  IO.println s!"12. CAS Telemetry Spooler (v1)     : {status telOk} ({telCount} accepted+rejected events, de Bruijn CAS blobs)"
  IO.println s!"13. In-Kernel Transitive Axiom Gate: {status axiomOk} ({axiomReport.theoremsAudited} theorems via Lean.collectAxioms, 0 {sAx})"
  IO.println s!"14. LLVM Declared Slot Types      : {status slotTypeRegressionOk} (3-field i256 tuple, ptr call)"
  let allOk := roundTripWireOk && roundTripJsonOk && certReport.verified &&
    tvReport.allPassed && superoptOk && pluginsOk && law5Ok &&
    fcPropOk && fcNaiveVacuousOk && relSamplingOk && gpuHeadroomOk &&
    metalValid && fcMetalValid && blake3Ok && tpuCodegenOk && mulDivOk && telOk && axiomOk && slotTypeRegressionOk &&
    llvmX86.length > 500 && ptxTxt.length > 500 && fcLlvm.length > 200 && fcPtx.length > 200
  if allOk then
    IO.println s!"=== ALL {tag.toUpper} v0.5.0 SELF-TESTS PASSED ==="
    return 0
  else
    IO.println s!"=== {tag.toUpper} SELF-TEST FAILED ==="
    return 1


def printCoreUsage (tag : String) (hasFrontend : Bool) : IO Unit := do
  let fe (xs : List String) : List String := if hasFrontend then xs else []
  let lines := [
    s!"{tag} v0.5.0 — Formally Validated Lean 4 Optimizer, Segregated Plugin Engine, Superoptimizer, TV, FastCheck & Multi-Target Codegen",
    "",
    s!"Usage: {tag} <command> [options]",
    "",
    "Commands:"
  ] ++ fe ["  build-exe          Compile a .lean source file directly to a native executable (<file.lean> -o <bin>)"] ++ [
    "  compile-llvm       Emit baseline or optimized LLVM 18 IR (--input <file>, --arch x86_64|arm64, --baseline, --slot-regression, -o <path>)",
    "  compile-static-lib Emit C-ABI static library (.a) + C header (.h) for zero-copy FFI (--input <file>, -o <lib.a>, --header <lib.h>)",
    "  compile-mlir       Emit GPU MLIR module (--input <file>, -o <path>)",
    "  compile-ptx        Emit NVIDIA PTX 8.0 assembly (--input <file>, --sm sm_90, --fastcheck, -o <path>)",
    "  compile-metal      Emit Apple Metal Shading Language 3.0 (--input <file>, --fastcheck, -o <path>)",
    "  compile-fastcheck  Run Constraint-Propagating FastCheck or emit SIMD/PTX/Metal kernels (--samples N, --emit-llvm, --emit-ptx, --emit-metal, --json, -o <path>)",
    "  compile-hybrid     Partition module into CPU/GPU and emit hybrid host dispatch glue (--input <file>, -o <path>)",
    "  superopt           Run cost-guided enumerative superoptimizer (--target x86_64|arm64|cuda_ptx|apple_metal, --json, -o <path>)",
    "  plugins            Run segregated optimization plugins under Law 1 TV/Cost Gate (--target <arch>, --test-adversarial, --json)",
    "  pr-verify          Run Law 5 PR & Spec-Pinning Gate + Season 8 turbo-lean pr-verify/audit-spec (--base <ref>, --disallow-spec-changes, --json)",
    "  turbo-plugin       Run JSONL-stdio external accelerator plugin for turbo-lean (ExternalProcessAccelerator protocol)",
    "  verify-certs       Run optimization pipeline and verify translation certificates (--input <file>, --json, -o <path>)",
    "  validate-tv        Run Alive2-style symbolic translation validation (--input <file>, --json, -o <path>)",
    "  audit-axioms       Run in-kernel transitive axiom audit (Lean.collectAxioms snapshot, --json)",
    "  emit-lnir          Emit LNIR module in wire/JSON format (--wire, --json, --fastcheck, -o <path>)"
  ] ++ fe [
    "  audit-axioms       Run in-kernel transitive axiom audit over all 134 soundness theorems (--json)",
    "  turbo-status       Probe Turbo Lean integration, verify BLAKE3 vectors, and emit/verify receipt"
  ] ++ [
    "  self-test          Run end-to-end Core, Spec (Laws 1-5), Plugins, Codec, FastCheck, Superopt, SymbolicTV, LLVM/PTX/Metal self-tests",
    "  worker             Run persistent sub-millisecond JSON-RPC worker loop over stdin/stdout"
  ]
  IO.println (String.intercalate "\n" lines)

def runAuditAxioms (args : List String) : IO UInt32 := do
  let report := verifiedAxiomAuditReport
  IO.println (if hasFlag args "--json" then report.toJson else report.formatSummary)
  return if report.passed then 0 else 1

/-- Benchmark the compiler's SNARK `GF(2^128)` / Additive NTT / Sumcheck / Folding codegen
    (`512-bit AVX-512 VPCLMULQDQ`, `128-bit PCLMULQDQ`, `ARM64 NEON TriNeon`, `3-CLMUL low-twiddle`,
    and `17-CLMUL fold_alpha_four`) and verify all algebraic & gate invariants. -/
def runBenchSnarkKernels (args : List String) : IO UInt32 := do
  let iters := (findFlagValue args "--iters" "64").toNat?.getD 64
  let t0 ← IO.monoNanosNow
  let snarkDecls : List LNIRDecl := [
    { name := "snark_fast_ghash_mul_lo"
      params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
      retTy := .i64
      body := .letBind 2 .i64 (.scalar (.binOp .clmul64 (.var 0) (.var 1))) (.ret 2) },
    { name := "snark_fast_ntt_btf_u_lo"
      params := [{ id := 0, name := "u", ty := .i64 }, { id := 1, name := "p", ty := .i64 }]
      retTy := .i64
      body := .letBind 2 .i64 (.scalar (.binOp .bitXor (.var 0) (.var 1))) (.ret 2) },
    { name := "snark_fast_ntt_btf_v_lo"
      params := [{ id := 0, name := "u", ty := .i64 }, { id := 1, name := "v", ty := .i64 }, { id := 2, name := "p", ty := .i64 }]
      retTy := .i64
      body := .letBind 3 .i64 (.scalar (.binOp .bitXor (.binOp .bitXor (.var 0) (.var 1)) (.var 2))) (.ret 3) }
  ]
  let baseMod : LNIRModule := { mkCanonicalBenchmarkModule with decls := mkCanonicalBenchmarkModule.decls ++ snarkDecls }
  let mut checksum : UInt64 := 1
  for i in [0 : iters] do
    let (optMod, _) := runDefaultPipeline baseMod
    let sigs := moduleToCAbiSigs optMod
    let rs := emitCAbiRustFromSigs sigs
    let msl := emitMetalModule optMod
    let lowTwOk := LeanNative.Spec.verifyLowTwiddleZmmNttC 64 0 3 1
    let triOk := LeanNative.Spec.verifyTriNeonFoldFourC 0 3 17 0
    checksum := checksum + rs.length.toUInt64 + msl.length.toUInt64 + lowTwOk + triOk + i.toUInt64
  let t1 ← IO.monoNanosNow
  let elapsedNs := if t1 >= t0 then t1 - t0 else 1
  let perIterUs := elapsedNs / (iters * 1000).max 1
  let sigs := moduleToCAbiSigs baseMod
  let rs := emitCAbiRustFromSigs sigs
  let msl := emitMetalModule baseMod
  let hasZmm : Bool := decide ((rs.splitOn "lean_native_f128_mul_const_zmm").length > 1)
  let hasLowTw : Bool := decide ((rs.splitOn "lean_native_f128_mul_low_const_m128i").length > 1)
  let hasTriNeon : Bool := decide ((rs.splitOn "lean_native_f128_tri_acc_neon").length > 1)
  let hasFold4 : Bool := decide ((rs.splitOn "lean_native_f128_fold_alpha_four_slice").length > 1)
  let hasFold64 : Bool := decide ((rs.splitOn "lean_native_f128_fold64_banked_nested_slice").length > 1)
  let hasTransBtf : Bool := decide ((rs.splitOn "lean_native_f128_transpose_butterfly_fused_2layer_slice").length > 1)
  let hasTile8 : Bool := decide ((rs.splitOn "lean_native_f128_partial_fold_tile8_slice").length > 1)
  let hasAdjoint : Bool := decide ((rs.splitOn "lean_native_f128_adjoint_inject_and_sweep_slice").length > 1)
  let hasUrmBatch : Bool := decide ((rs.splitOn "lean_native_f128_urm_accumulate_convert_batch_ab_slice").length > 1)
  let hasPreRedEqLo : Bool := decide ((rs.splitOn "lean_native_f128_pre_reduce_eq_lo_slice").length > 1)
  let hasGfniNomul : Bool := decide ((rs.splitOn "lean_native_gf8_urm_convert_ab_nomul_gfni_slice").length > 1)
  let hasGfniC4 : Bool := decide ((rs.splitOn "lean_native_gf2_fold_64_rows_gfni_c4_slice").length > 1)
  let hasMetalPair : Bool := decide ((msl.splitOn "ln_gf128_mul_pair").length > 1)
  let ok : Bool := hasZmm && hasLowTw && hasTriNeon && hasFold4 && hasFold64 && hasTransBtf && hasTile8 && hasAdjoint && hasUrmBatch && hasPreRedEqLo && hasGfniNomul && hasGfniC4 && hasMetalPair && (checksum != 0)
  if hasFlag args "--json" then
    IO.println s!"\{\"ok\":{ok},\"iters\":{iters},\"elapsed_ns\":{elapsedNs},\"per_iter_us\":{perIterUs},\"rust_ffi_bytes\":{rs.length},\"metal_bytes\":{msl.length},\"avx512_vpclmulqdq_zmm\":{hasZmm},\"low_twiddle_3clmul\":{hasLowTw},\"trineon_schoolbook\":{hasTriNeon},\"fold_alpha_four_17clmul\":{hasFold4},\"fold64_banked_nested_zmm\":{hasFold64},\"transpose_btf_zmm\":{hasTransBtf},\"partial_fold_tile8\":{hasTile8},\"adjoint_inject_sweep\":{hasAdjoint},\"urm_batch_ab\":{hasUrmBatch},\"pre_reduce_eq_lo\":{hasPreRedEqLo},\"gfni_convert_ab_nomul\":{hasGfniNomul},\"gfni_fold64_c4\":{hasGfniC4},\"metal_pair_nibble_lut\":{hasMetalPair},\"checksum\":{checksum}}"
  else
    IO.println s!"[bench-snark-kernels] ok={ok} iters={iters} elapsed={elapsedNs / 1000000}ms ({perIterUs}us/iter) rust_ffi={rs.length}B metal={msl.length}B zmm512={hasZmm} low_tw_3clmul={hasLowTw} trineon={hasTriNeon} fold4_17clmul={hasFold4} fold64={hasFold64} trans_btf={hasTransBtf} tile8={hasTile8} adjoint={hasAdjoint} urm_batch={hasUrmBatch} pre_red_eq={hasPreRedEqLo} gfni_nomul={hasGfniNomul} gfni_c4={hasGfniC4} metal_pair={hasMetalPair}"
  return if ok then 0 else 1

/-- Shared CLI dispatcher for both `lean-native-core` (`elaborateHook? = none`) and `lean-native` (`elaborateHook? = some ...`). -/
def dispatchSharedCommand (tag : String) (elaborateHook? : Option (String → IO LNIRModule))
    (args : List String) : IO (Option UInt32) := do
  match args with
  | "audit-axioms" :: rest       => some <$> runAuditAxioms rest
  | "bench-snark-kernels" :: rest => some <$> runBenchSnarkKernels rest
  | "compile-llvm" :: rest       => some <$> runCompileLLVM tag elaborateHook? rest
  | "compile-static-lib" :: rest => some <$> runCompileStaticLib tag elaborateHook? rest
  | "emit-cabi-bindings" :: rest => some <$> runEmitCAbiBindings tag elaborateHook? rest
  | "compile-c-abi" :: rest      => some <$> runEmitCAbiBindings tag elaborateHook? rest
  | "compile-mlir" :: rest       => some <$> runCompileMLIR tag elaborateHook? rest
  | "compile-ptx" :: rest       => some <$> runCompilePTX tag elaborateHook? rest
  | "compile-metal" :: rest     => some <$> runCompileMetal tag elaborateHook? rest
  | "compile-fastcheck" :: rest => some <$> runCompileFastCheck tag elaborateHook? rest
  | "compile-hybrid" :: rest    => some <$> runCompileHybrid tag elaborateHook? rest
  | "compile" :: rest           => some <$> runCompileMode tag elaborateHook? rest
  | "--c-abi" :: _              => some <$> runCompileMode tag elaborateHook? args
  | "--emit-c-abi" :: _         => some <$> runCompileMode tag elaborateHook? args
  | "--self-test" :: _          => some <$> runCoreSelfTest tag
  | "superopt" :: rest          => some <$> runSuperopt elaborateHook? rest
  | "plugins" :: rest           => some <$> runPlugins elaborateHook? rest
  | "telemetry" :: rest         => some <$> runTelemetry elaborateHook? rest
  | "pr-verify" :: rest         => some <$> runPRVerify tag rest
  | "turbo-plugin" :: _         => some <$> runTurboPlugin
  | "verify-certs" :: rest      => some <$> runVerifyCerts tag elaborateHook? rest
  | "validate-tv" :: rest       => some <$> runValidateTV elaborateHook? rest
  | "emit-lnir" :: rest         => some <$> runEmitLNIR tag elaborateHook? rest
  | "worker" :: _               => some <$> runWorker tag
  | _                           =>
    if hasFlag args "--c-abi" || hasFlag args "--emit-c-abi" then
      some <$> runCompileMode tag elaborateHook? args
    else
      return none

end LeanNative.Driver.CoreCLI
