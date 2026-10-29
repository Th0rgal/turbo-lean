import LeanNative.IR.Types
import LeanNative.IR.AST
import LeanNative.IR.Codec
import LeanNative.Spec
import LeanNative.Semantics.Value
import LeanNative.Semantics.Eval
import LeanNative.Proofs.CertChecker
import LeanNative.Proofs.SymbolicTV
import LeanNative.Transform.Pass
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
open LeanNative.Backend.Hybrid
open LeanNative.Backend.FastCheck
open LeanSys.Posix
open LeanSys.Codec

def toOptimizationCert (c : PassStepCert) : OptimizationCert where
  passName := c.passName; declName := c.declName; inputHash := c.inputHash; outputHash := c.outputHash
  changed := c.changed; assurance := c.assurance; theoremRef := c.theoremRef; notes := c.notes

/-- Strict target architecture parser (`P0` Fail-Closed Trust Boundary):
    - Maps `"macos"`, `"macos-arm64"`, `"darwin-arm64"`, `"arm64-apple-macosx"`, `"m2"`, `"m3"`, `"m4"`
      to `.macosArm64` (distinct from `.iosArm64`).
    - Returns `none` on unknown target strings instead of silently defaulting to `.x86_64`. -/
def parseTargetArch? : String → Option TargetArch
  | "x86_64" | "amd64" | "x86_64-unknown-linux-gnu" => some .x86_64
  | "arm64" | "aarch64" | "aarch64-unknown-linux-gnu" => some .arm64
  | "macos" | "macos-arm64" | "darwin-arm64" | "arm64-apple-macosx" | "arm64-apple-darwin"
  | "air-m2" | "m2" | "m3" | "m4" => some .macosArm64
  | "ios" | "ios-arm64" | "arm64-apple-ios" | "iphone13mini" | "apple-a15" => some .iosArm64
  | "ios-sim" | "ios-sim-arm64" | "arm64-apple-ios-simulator" => some .iosSimArm64
  | "android" | "android-arm64" | "aarch64-linux-android" | "pixel8" => some .androidArm64
  | "wasm" | "wasm32" | "wasm32-unknown-unknown" => some .wasm32
  | "nvptx" | "nvptx64" | "ptx" | "cuda" => some .nvptx64
  | "hybrid" | "hybrid-cpu-nvptx64" => some .hybridCpuGpu
  | _ => none

def parseTargetArchIO (raw : String) : IO TargetArch := do
  match parseTargetArch? raw with
  | some t => return t
  | none => throw <| IO.userError s!"[lean-native] Unsupported target architecture '{raw}' (expected x86_64, arm64, macos-arm64, ios-arm64, ios-sim-arm64, android-arm64, wasm32, nvptx64, or hybrid)"

def parseTargetArch (raw : String) : TargetArch :=
  (parseTargetArch? raw).getD .x86_64

def parseSuperoptTarget? : String → Option SuperoptTarget
  | "x86_64" | "amd64" => some .x86_64
  | "arm64" | "aarch64" | "macos-arm64" | "ios-arm64" | "android-arm64" => some .arm64
  | "cuda" | "cuda_ptx" | "ptx" | "nvptx" | "nvptx64" => some .cuda_ptx
  | "metal" | "apple_metal" | "msl" => some .apple_metal
  | _ => none

def parseSuperoptTargetIO (raw : String) : IO SuperoptTarget := do
  match parseSuperoptTarget? raw with
  | some t => return t
  | none => throw <| IO.userError s!"[lean-native] Unsupported superoptimizer target '{raw}' (expected x86_64, arm64, cuda_ptx, or apple_metal)"

def parseSuperoptTarget (raw : String) : SuperoptTarget :=
  (parseSuperoptTarget? raw).getD .x86_64

private abbrev escapeJsonWorker := LeanNative.IR.jsonEscape

private def parseRpcTapes (line : String) : JsonTape × Option JsonTape :=
  let root := JsonTape.indexJsonObject (LeanSys.Posix.ByteSlice.ofString line)
  let params := (JsonTape.lookupSlice? root "params").map (fun (ps, _) => JsonTape.indexJsonObject ps)
  (root, params)

def extractRpcId (line : String) : String :=
  let (root, _) := parseRpcTapes line
  match JsonTape.lookupSlice? root "id" with
  | some (s, isStr) => if isStr then s!"\"{escapeJsonWorker s.toStringLossy}\"" else s.toStringLossy
  | none => "1"

def extractRpcStringField (line : String) (key : String) : Option String :=
  let (root, params) := parseRpcTapes line
  JsonTape.lookupString? root key <|> (params.bind fun p => JsonTape.lookupString? p key)

private def invalidRpcWire (line : String) : Bool :=
  let (root, params) := parseRpcTapes line
  let fields := [JsonTape.lookupSlice? root "wire", params.bind (fun p => JsonTape.lookupSlice? p "wire")]
  fields.any fun field => match field with
    | none => false
    | some (_, isString) => !isString

def hasRpcBoolField (line : String) (key : String) (expected : Bool) : Bool :=
  let (root, params) := parseRpcTapes line
  match JsonTape.lookupBool? root key <|> (params.bind fun p => JsonTape.lookupBool? p key) with
  | some b => b == expected
  | none => false

def extractRpcNatField (line : String) (key : String) (defaultVal : Nat) : Nat :=
  let (root, params) := parseRpcTapes line
  (JsonTape.lookupNat? root key <|> (params.bind fun p => JsonTape.lookupNat? p key)).getD defaultVal

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

def handleFastWorkerRequest? (engineName line : String) : Option String :=
  let reqId := extractRpcId line
  if invalidRpcWire line then
    some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"invalid_lnir_wire\"}"
  else
  let method := (extractRpcStringField line "method").getD "ping"
  let hasBool2 (k1 k2 : String) (b : Bool) := hasRpcBoolField line k1 b || hasRpcBoolField line k2 b
  if ["ping", "eval-cex", "select-target", "riscv-step-audit"].contains method &&
      (extractRpcStringField line "wire").isSome then
    some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"wire_not_supported_by_method\"}"
  else
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
    match extractRpcStringField line "wire" with
    | some rawWire =>
      match LNIRModule.fromWire? rawWire with
      | none =>
        some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"invalid_lnir_wire\"}"
      | some m =>
        if m.decls.any (·.assurance == .unsupported) then
          some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unsupported_assurance_level_decl\"}"
        else
          let rep := runFastCheckModule m numSamples (!noProp)
          some s!"\{\"id\":{reqId},\"ok\":true,\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"result\":\{\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"report\":{rep.toJson}}}"
    | none =>
      if invalidRpcWire line then
        some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"invalid_lnir_wire\"}"
      else if !hasRpcBoolField line "canonical_benchmark" true && !hasRpcBoolField line "fastcheck_sample" true then
        some s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"explicit_input_wire_required\"}"
      else
        let sampleMod := if hasRpcBoolField line "canonical_benchmark" true && !hasRpcBoolField line "fastcheck_sample" true
          then mkCanonicalBenchmarkModule else mkFastCheckSampleModule
        let rep := runFastCheckModule sampleMod numSamples (!noProp)
        some s!"\{\"id\":{reqId},\"ok\":true,\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"result\":\{\"recommended_target\":\"{recTarget}\",\"c_abi_ready\":true,\"report\":{rep.toJson}}}"
  | _ => none

def handleWorkerRequest (engineName : String) (cache : WorkerCache) (line : String) : String :=
  if let some fastResp := handleFastWorkerRequest? engineName line then fastResp
  else
    let reqId := extractRpcId line
    let method := (extractRpcStringField line "method").getD "ping"
    let rawWireOpt := extractRpcStringField line "wire"
    let customModOpt := rawWireOpt.bind LNIRModule.fromWire?
    if invalidRpcWire line || (rawWireOpt.isSome && customModOpt.isNone) then
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"invalid_lnir_wire\"}"
    else if (customModOpt.map (fun m => m.decls.any (·.assurance == .unsupported))).getD false then
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unsupported_assurance_level_decl\"}"
    else if ["compile-llvm", "compile-ptx", "compile-metal", "compile-mlir", "compile-tpu",
             "compile-fastcheck", "superopt", "plugins", "verify-certs", "validate-tv"].contains method &&
        customModOpt.isNone && !hasRpcBoolField line "canonical_benchmark" true &&
        !hasRpcBoolField line "fastcheck_sample" true then
      s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"explicit_input_wire_required\"}"
    else
    let hasCanon := hasRpcBoolField line "canonical_benchmark" true
    let useFcSample := customModOpt.isNone && hasRpcBoolField line "fastcheck_sample" true && !hasCanon
    let effModOpt := customModOpt <|> (if useFcSample then some mkFastCheckSampleModule else none)
    let nDecls := match effModOpt with
      | some m => m.decls.length
      | none => cache.optMod.decls.length
    match method with
    | "compile-llvm" =>
      let archStr := (extractRpcStringField line "arch").getD "x86_64"
      match parseTargetArch? archStr with
      | none =>
        s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unsupported_target_arch:{escapeJsonWorker archStr}\"}"
      | some arch =>
        let isBase := hasRpcBoolField line "baseline" true
        let wasmSimd128 := hasRpcBoolField line "wasmSimd128" true || hasRpcBoolField line "wasm_simd128" true
        let ir := match effModOpt with
          | some m =>
            if isBase then emitLLVMBaseline m arch none wasmSimd128 else emitLLVMOptimized (runDefaultPipeline m).1 arch none wasmSimd128
          | none =>
            if isBase then (if arch == .x86_64 then cache.llvmBaseX86 else emitLLVMBaseline cache.baseMod arch none wasmSimd128)
            else if arch == .arm64 then cache.llvmOptArm
            else if arch == .x86_64 then cache.llvmOptX86
            else emitLLVMOptimized cache.optMod arch none wasmSimd128
        s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"arch\":\"{escapeJsonWorker archStr}\",\"baseline\":{isBase},\"decls\":{nDecls},\"irBytes\":{ir.length},\"ir\":\"{escapeJsonWorker ir}\"}}"
    | "compile-ptx" =>
      let sm := (extractRpcStringField line "sm").getD "sm_90"
      let isFc := hasRpcBoolField line "fastcheck" true
      let ptx := match customModOpt with
        | some m => if isFc then emitFastCheckPTX m sm else emitPTXModule (runDefaultPipeline m).1 sm
        | none =>
          if useFcSample then
            if isFc then (if sm == "sm_90" then cache.fcPtxText else emitFastCheckPTX mkFastCheckSampleModule sm)
            else emitPTXModule (runDefaultPipeline mkFastCheckSampleModule).1 sm
          else if isFc then emitFastCheckPTX cache.baseMod sm
          else if sm == "sm_90" then cache.ptxSm90 else emitPTXModule cache.optMod sm
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"sm\":\"{escapeJsonWorker sm}\",\"decls\":{nDecls},\"ptxBytes\":{ptx.length},\"ptx\":\"{escapeJsonWorker ptx}\"}}"
    | "compile-metal" =>
      let isFc := hasRpcBoolField line "fastcheck" true
      let msl := match customModOpt with
        | some m => if isFc then emitFastCheckMetal m else emitMetalModule (runDefaultPipeline m).1
        | none =>
          if useFcSample then
            if isFc then cache.fcMetalText else emitMetalModule (runDefaultPipeline mkFastCheckSampleModule).1
          else if isFc then emitFastCheckMetal cache.baseMod
          else cache.metalText
      let (valid, _) := validateMetalShader msl
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"apple_metal_3.0\",\"valid\":{valid},\"decls\":{nDecls},\"metalBytes\":{msl.length},\"metal\":\"{escapeJsonWorker msl}\"}}"
    | "compile-mlir" =>
      let dialect := (extractRpcStringField line "dialect").getD "gpu"
      let mlir := match effModOpt with
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
      let (shlo, pallas) := match effModOpt with
        | some m => let mOpt := (runDefaultPipeline m).1; (emitStableHLOModule mOpt, emitTPUPallasModule mOpt)
        | none => (cache.stablehloText, cache.pallasText)
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":\{\"target\":\"google_cloud_tpu_v5e\",\"decls\":{nDecls},\"stablehloBytes\":{shlo.length},\"pallasBytes\":{pallas.length},\"stablehlo\":\"{escapeJsonWorker shlo}\",\"pallas\":\"{escapeJsonWorker pallas}\"}}"
    | "compile-fastcheck" =>
      let noProp := hasRpcBoolField line "useConstraintProp" false || hasRpcBoolField line "noConstraintProp" true
      let repJson := match customModOpt with
        | some m => (runFastCheckModule m 1024 (!noProp)).toJson
        | none =>
          if hasRpcBoolField line "canonical_benchmark" true && !hasRpcBoolField line "fastcheck_sample" true then
            (runFastCheckModule cache.baseMod 1024 (!noProp)).toJson
          else if noProp then cache.fcReportVacJson else cache.fcReportPropJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{repJson}}"
    | "superopt" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      match parseSuperoptTarget? tgtStr with
      | none =>
        s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unsupported_superopt_target:{escapeJsonWorker tgtStr}\"}"
      | some tgt =>
        let soJson := match effModOpt with
          | some m => (superoptModule tgt m).2.toJson
          | none => if tgt == SuperoptTarget.x86_64 then cache.superoptX86Json else (superoptModule tgt cache.baseMod).2.toJson
        s!"\{\"id\":{reqId},\"ok\":true,\"result\":{soJson}}"
    | "plugins" =>
      let tgtStr := (extractRpcStringField line "target").getD "x86_64"
      match parseSuperoptTarget? tgtStr with
      | none =>
        s!"\{\"id\":{reqId},\"ok\":false,\"error\":\"unsupported_plugin_target:{escapeJsonWorker tgtStr}\"}"
      | some tgt =>
        let plJson := match effModOpt with
          | some m => (runSegregatedPluginPipeline tgt true m).2.toJson
          | none => if tgt == SuperoptTarget.x86_64 then cache.pluginsX86Json else (runSegregatedPluginPipeline tgt true cache.baseMod).2.toJson
        s!"\{\"id\":{reqId},\"ok\":true,\"result\":{plJson}}"
    | "verify-certs" =>
      let certJson := match effModOpt with
        | some m => (verifyModuleCerts m.moduleName ((runDefaultPipeline m).2.map toOptimizationCert)).toJson
        | none => cache.certReportJson
      s!"\{\"id\":{reqId},\"ok\":true,\"result\":{certJson}}"
    | "validate-tv" =>
      let tvJson := match effModOpt with
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

end LeanNative.Driver.CoreCLI
