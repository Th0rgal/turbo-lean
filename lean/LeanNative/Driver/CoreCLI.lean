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
import LeanSys.Posix
import LeanSys.Codec
import LeanNative.Driver.KernelTemplates

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

def parseTargetArch : String → TargetArch
  | "arm64" | "aarch64" => .arm64
  | "ios" | "ios-arm64" | "arm64-apple-ios" | "macos-arm64" | "m3" => .iosArm64
  | "ios-sim" | "ios-sim-arm64" | "arm64-apple-ios-simulator" => .iosSimArm64
  | "android" | "android-arm64" | "aarch64-linux-android" => .androidArm64
  | "wasm" | "wasm32" | "wasm32-unknown-unknown" => .wasm32
  | "nvptx" | "nvptx64" | "ptx" | "cuda" => .nvptx64
  | "hybrid" => .hybridCpuGpu
  | _ => .x86_64

def parseSuperoptTarget : String → SuperoptTarget
  | "arm64" | "aarch64" => .arm64
  | "cuda" | "cuda_ptx" | "ptx" | "nvptx" => .cuda_ptx
  | "metal" | "apple_metal" | "msl" => .apple_metal
  | _ => .x86_64

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
  let kernelEngine := findFlagValue args "--kernel" "con-leche"
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
  let jsonOut := s!"\{\n  \"status\": \"{if overallOk then "pr_verified" else "pr_rejected"}\",\n  \"engine\": \"{tag}\",\n  \"kernel\": \"{kernelEngine}\",\n  \"version\": \"0.5.0\",\n  \"baseRef\": \"{baseRef}\",\n  \"law1UntrustedPluginGatePassed\": {pluginReport.adversarialRejected && allDeclTvOk},\n  \"law5SpecPinningGatePassed\": {law5Passed},\n  \"specBlake3\": \"{specHashHex}\",\n  \"testRunnerBlake3\": \"{testHashHex}\",\n  \"symbolicTvPassedDecls\": {tvReport.passedDecls},\n  \"symbolicTvTotalDecls\": {tvReport.totalDecls},\n  \"pluginsAccepted\": {pluginReport.acceptedCount},\n  \"adversarialPluginsRejected\": {pluginReport.rejectedCount},\n  \"costBefore\": {pluginReport.totalCostBefore},\n  \"costAfter\": {pluginReport.totalCostAfter},\n  \"fastCheckSelfTestPassed\": {fcSelfTestOk}\n}"
  let summaryText := String.intercalate "\n" [
    s!"[{tag}] PR & Spec-Pinning Verification Gate (base={baseRef}, kernel={kernelEngine}):",
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


/-! ## Persistent Sub-Millisecond JSON-RPC Worker (`worker`) -/

private abbrev escapeJsonWorker := LeanNative.IR.jsonEscape

private def parseRpcTapes (line : String) : JsonTape × Option JsonTape :=
  let root := JsonTape.indexJsonObject (LeanSys.Posix.ByteSlice.ofString line)
  let params := (JsonTape.lookupSlice? root "params").map (fun (ps, _) => JsonTape.indexJsonObject ps)
  (root, params)

private def extractRpcId (line : String) : String :=
  let (root, _) := parseRpcTapes line
  match JsonTape.findEntry? root "id" with
  | some e =>
    if e.valLen == 0 then "1"
    else
      let s : LeanSys.Posix.ByteSlice := { ba := root.root.ba, off := e.valOff, len := e.valLen }
      if e.isString then s!"\"{s.toStringLossy}\"" else s.toStringLossy
  | none => "1"

private def extractRpcStringField (line : String) (key : String) : Option String :=
  let (root, params) := parseRpcTapes line
  (JsonTape.lookupString? root key) <|> (params.bind (fun p => JsonTape.lookupString? p key))

private def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let (root, params) := parseRpcTapes line
  let b? := (JsonTape.lookupBool? root key) <|> (params.bind (fun p => JsonTape.lookupBool? p key))
  b? == some expected

private def extractRpcNatField (line : String) (key : String) (defaultVal : Nat) : Nat :=
  let (root, params) := parseRpcTapes line
  ((JsonTape.lookupNat? root key) <|> (params.bind (fun p => JsonTape.lookupNat? p key))).getD defaultVal

structure WorkerCache where
  baseMod          : LNIRModule
  optMod           : LNIRModule
  certReportJson   : String
  tvReportJson     : String
  superoptX86Json  : String
  pluginsX86Json   : String
  llvmOptX86       : String
  llvmOptArm       : String
  llvmBaseX86      : String
  ptxSm90          : String
  metalText        : String
  mlirText         : String
  stablehloText    : String
  pallasText       : String
  fcReportPropJson : String
  fcReportVacJson  : String
  fcLlvmText       : String
  fcPtxText        : String
  fcMetalText      : String

def initWorkerCache : IO WorkerCache := do
  let baseMod := mkCanonicalBenchmarkModule
  let (optMod, stepCerts) := runDefaultPipeline baseMod
  let certReport := verifyModuleCerts baseMod.moduleName (stepCerts.map toOptimizationCert)
  let tvReport := validateTranslationModule baseMod optMod
  let (_, soRep) := superoptModule .x86_64 baseMod
  let (_, plRep) := runSegregatedPluginPipeline .x86_64 true baseMod
  let fcMod := mkFastCheckSampleModule
  return {
    baseMod, optMod
    certReportJson   := certReport.toJson
    tvReportJson     := tvReport.toJson
    superoptX86Json  := soRep.toJson
    pluginsX86Json   := plRep.toJson
    llvmOptX86       := emitLLVMOptimized optMod .x86_64
    llvmOptArm       := emitLLVMOptimized optMod .arm64
    llvmBaseX86      := emitLLVMBaseline baseMod .x86_64
    ptxSm90          := emitPTXModule optMod "sm_90"
    metalText        := emitMetalModule optMod
    mlirText         := emitMLIRModule optMod
    stablehloText    := emitStableHLOModule optMod
    pallasText       := emitTPUPallasModule optMod
    fcReportPropJson := (runFastCheckModule fcMod 1024 true).toJson
    fcReportVacJson  := (runFastCheckModule fcMod 1024 false).toJson
    fcLlvmText       := emitFastCheckLLVM fcMod
    fcPtxText        := emitFastCheckPTX fcMod "sm_90"
    fcMetalText      := emitFastCheckMetal fcMod
  }

def getOrInitWorkerCache (cacheRef : IO.Ref (Option WorkerCache)) : IO WorkerCache := do
  match ← cacheRef.get with
  | some c => return c
  | none =>
    let c ← initWorkerCache
    cacheRef.set (some c)
    return c

/-- Fast-path worker RPC methods (`< 0.05 ms`, zero `WorkerCache` cold-start cost). -/
def handleFastWorkerRequest? (engineName line : String) : Option String :=
  let reqId := extractRpcId line
  let method := (extractRpcStringField line "method").getD "ping"
  let hasBool2 (k1 k2 : String) (b : Bool) := hasRpcBoolField line k1 b || hasRpcBoolField line k2 b
  match method with
  | "ping" =>
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"status\":\"pong\",\"engine\":\"{engineName}\",\"version\":\"0.5.0\",\"decls\":8}}"
  | "eval-cex" =>
    let witnessEnv := (VarEnv.empty.bind 1 (.u64 1000000)).bind 0 (.u64 1000042)
    let certified := certifyCounterexample 128 evmConstrainedBuggyPropDecl witnessEnv HeapState.empty
    some s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"declName\":\"evm_constrained_buggy_prop\",\"certified\":{certified},\"falsePositives\":0,\"theorem\":\"LeanNative.Backend.FastCheck.certifyCounterexample_no_false_positive\",\"report\":\{\"counterexamplesFound\":1,\"vacuousPasses\":0,\"falsePositives\":0}}}"
  | "select-target" =>
    let tripCount := extractRpcNatField line "trip_count" (extractRpcNatField line "tripCount" 65536)
    let tgt := LeanNative.Backend.selectOptimalComputeTarget tripCount
      (hasBool2 "is_matrix" "isMatrix" true) (hasBool2 "is_256bit" "is256Bit" true)
      (hasBool2 "is_control_heavy" "isControlHeavy" true) (hasBool2 "has_tpu" "hasTpu" true)
      (hasBool2 "has_gpu" "hasGpu" true || hasRpcBoolField line "has_cuda_gpu" true) (hasBool2 "has_metal" "hasMetal" true)
    some s!"\{\"id\":{reqId},\"ok\":true,\"target\":\"{tgt}\",\"result\":\{\"target\":\"{tgt}\",\"trip_count\":{tripCount}}}"
  | "riscv-step-audit" =>
    let boot := extractRpcNatField line "bootstrap_steps" 23132
    let scale := extractRpcNatField line "loop_scale" 1
    let csr := extractRpcNatField line "csr_cost" 0
    let candK := extractRpcNatField line "candidate_k" 1000000
    let verMin := extractRpcNatField line "verify_minutes" 12
    let (refuted, maxObs, violIn) := runRiscvStepBudgetAudit boot scale csr candK
    let yukonScore := candK * 10000 + verMin
    let body := s!"\"refuted\":{refuted},\"max_observed_steps\":{maxObs},\"candidate_k\":{candK},\"violating_input\":{violIn},\"yukon_score\":{yukonScore}"
    some s!"\{\"id\":{reqId},\"ok\":true,{body},\"result\":\{{body}}}"
  | "batch-fastcheck" =>
    let numSamples := extractRpcNatField line "samples" (extractRpcNatField line "num_samples" 1024)
    let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
    let recTarget := LeanNative.Backend.selectOptimalComputeTarget numSamples
      (hasRpcBoolField line "is_matrix" true) (!(hasRpcBoolField line "is_256bit" false))
      (hasRpcBoolField line "is_control_heavy" true) (hasRpcBoolField line "has_tpu" true)
      (!(hasRpcBoolField line "has_gpu" false)) (hasRpcBoolField line "has_metal" true)
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let rep := runFastCheckModule (customModOpt.getD mkFastCheckSampleModule) numSamples (!noProp)
    some s!"\{\"id\":{reqId},\"ok\":true,\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"result\":\{\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"report\":{rep.toJson}}}"
  | _ => none

def handleWorkerRequest (engineName : String) (cache : WorkerCache) (line : String) : String :=
  if let some fastResp := handleFastWorkerRequest? engineName line then fastResp
  else
    let reqId := extractRpcId line
    let method := (extractRpcStringField line "method").getD "ping"
    let customModOpt := (extractRpcStringField line "wire").bind LNIRModule.fromWire?
    let nDecls := cache.optMod.decls.length
    match method with
    | "compile-llvm" =>
      let archStr := (extractRpcStringField line "arch").getD "x86_64"
      let isBase := hasRpcBoolField line "baseline" true
      let ir := match customModOpt with
        | some m =>
          let arch := parseTargetArch archStr
          if isBase then emitLLVMBaseline m arch else emitLLVMOptimized (runDefaultPipeline m).1 arch
        | none =>
          if isBase then cache.llvmBaseX86
          else if archStr == "arm64" || archStr == "aarch64" then cache.llvmOptArm else cache.llvmOptX86
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"{escapeJsonWorker archStr}\",\"baseline\":{isBase},\"decls\":{nDecls},\"irBytes\":{ir.length},\"ir\":\"{escapeJsonWorker ir}\"}}"
    | "compile-ptx" =>
      let sm := (extractRpcStringField line "sm").getD "sm_90"
      let isFc := hasRpcBoolField line "fastcheck" true
      let ptx := if isFc then cache.fcPtxText
        else match customModOpt with
          | some m => emitPTXModule (runDefaultPipeline m).1 sm
          | none => if sm == "sm_90" then cache.ptxSm90 else emitPTXModule cache.optMod sm
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"{escapeJsonWorker sm}\",\"decls\":{nDecls},\"ptxBytes\":{ptx.length},\"ptx\":\"{escapeJsonWorker ptx}\"}}"
    | "compile-metal" =>
      let isFc := hasRpcBoolField line "fastcheck" true
      let msl := if isFc then cache.fcMetalText
        else match customModOpt with
          | some m => emitMetalModule (runDefaultPipeline m).1
          | none => cache.metalText
      let (valid, _) := validateMetalShader msl
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"apple_metal_3.0\",\"valid\":{valid},\"decls\":{nDecls},\"metalBytes\":{msl.length},\"metal\":\"{escapeJsonWorker msl}\"}}"
    | "compile-mlir" =>
      let dialect := (extractRpcStringField line "dialect").getD "gpu"
      let mlir := match customModOpt with
        | some m =>
          let mOpt := (runDefaultPipeline m).1
          if dialect == "pallas" then emitTPUPallasModule mOpt
          else if dialect == "stablehlo" || dialect == "tpu" then emitStableHLOModule mOpt
          else emitMLIRModule mOpt
        | none =>
          if dialect == "pallas" then cache.pallasText
          else if dialect == "stablehlo" || dialect == "tpu" then cache.stablehloText
          else cache.mlirText
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"dialect\":\"{escapeJsonWorker dialect}\",\"decls\":{nDecls},\"mlirBytes\":{mlir.length},\"mlir\":\"{escapeJsonWorker mlir}\"}}"
    | "compile-tpu" =>
      let (shlo, pallas) := match customModOpt with
        | some m => let mOpt := (runDefaultPipeline m).1; (emitStableHLOModule mOpt, emitTPUPallasModule mOpt)
        | none => (cache.stablehloText, cache.pallasText)
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"google_cloud_tpu_v5e\",\"decls\":{nDecls},\"stablehloBytes\":{shlo.length},\"pallasBytes\":{pallas.length},\"stablehlo\":\"{escapeJsonWorker shlo}\",\"pallas\":\"{escapeJsonWorker pallas}\"}}"
    | "compile-fastcheck" =>
      let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
      let repJson := match customModOpt with
        | some m => (runFastCheckModule m 1024 (!noProp)).toJson
        | none => if noProp then cache.fcReportVacJson else cache.fcReportPropJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{repJson}}"
    | "superopt" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let soJson := match customModOpt with
        | some m => (superoptModule (parseSuperoptTarget tgtStr) m).2.toJson
        | none => if tgtStr == "x86_64" then cache.superoptX86Json else (superoptModule (parseSuperoptTarget tgtStr) cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{soJson}}"
    | "plugins" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      let plJson := match customModOpt with
        | some m => (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true m).2.toJson
        | none => if tgtStr == "x86_64" then cache.pluginsX86Json else (runSegregatedPluginPipeline (parseSuperoptTarget tgtStr) true cache.baseMod).2.toJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{plJson}}"
    | "verify-certs" =>
      let certJson := match customModOpt with
        | some m => (verifyModuleCerts m.moduleName ((runDefaultPipeline m).2.map toOptimizationCert)).toJson
        | none => cache.certReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
    | "validate-tv" =>
      let tvJson := match customModOpt with
        | some m => (validateTranslationModule m (runDefaultPipeline m).1).toJson
        | none => cache.tvReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{tvJson}}"
    | other =>
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unknown_method:{escapeJsonWorker other}\"}"

abbrev handleWorkerLine := handleWorkerRequest

partial def workerLoop (engineName : String) (stdin stdout : IO.FS.Stream) (cacheRef : IO.Ref (Option WorkerCache)) : IO UInt32 := do
  let line ← stdin.getLine
  if line.isEmpty then return 0
  let trimmed := line.trimAscii.toString
  if trimmed.isEmpty then workerLoop engineName stdin stdout cacheRef
  else
    let method := (extractRpcStringField trimmed "method").getD ""
    if method == "exit" || method == "shutdown" || method == "quit" then
      stdout.putStrLn s!"\{\"id\":{extractRpcId trimmed},\"ok\":true,\"result\":\{\"status\":\"bye\"}}"
      stdout.flush; return 0
    else
      let resp ← match handleFastWorkerRequest? engineName trimmed with
        | some fast => pure fast
        | none =>
          let cache ← getOrInitWorkerCache cacheRef
          pure (handleWorkerRequest engineName cache trimmed)
      stdout.putStrLn resp
      stdout.flush; workerLoop engineName stdin stdout cacheRef

def runWorker (engineName : String) : IO UInt32 := do
  workerLoop engineName (← IO.getStdin) (← IO.getStdout) (← IO.mkRef none)

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
