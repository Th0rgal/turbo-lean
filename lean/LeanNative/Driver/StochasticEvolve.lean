import LeanNative.IR.Codec
import LeanNative.Transform.StochasticCert
import LeanNative.Transform.StochasticCertPass
import LeanNative.Transform.LoopVectorizeOpt
import LeanNative.Driver.CAbiEmit
import TurboLean.Blake3

set_option autoImplicit false

namespace LeanNative.Driver.CoreCLI

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Transform

def defaultEvolveGenerations : Nat := 8
def maxEvolveGenerations : Nat := 4096
def defaultEvolveSeed : UInt64 := 42

private def decodeStochasticPack? (bytes : ByteArray) : Option CertifiedRuleBundle := do
  if bytes.size < 16 || bytes.extract 0 8 != ByteArray.mk #[84, 76, 80, 75, 0, 0, 0, 2] then none else
    let headerLen := (List.range 8).foldl (fun n i => n + bytes[i + 8]!.toNat * 256 ^ i) 0
    let start := 16 + headerLen
    if start > bytes.size then none else
      let header ← String.fromUTF8? (bytes.extract 16 start)
      let normalized ← normalizePackJson header
      let manifest ← StochasticJson.parse? normalized
      guard ((← StochasticJson.nat? (← StochasticJson.field? manifest "format_version")) == 2)
      let _ ← StochasticJson.array? (← StochasticJson.field? manifest "actions")
      let blobs ← StochasticJson.array? (← StochasticJson.field? manifest "blobs")
      let (endOffset, bundles) ← blobs.foldlM (fun (offset, found) blob => do
        let size ← StochasticJson.nat? (← StochasticJson.field? blob "size_bytes")
        guard (offset + size ≤ bytes.size)
        let hash ← StochasticJson.string? (← StochasticJson.field? blob "blob_hash")
        let payload := bytes.extract offset (offset + size)
        guard (hash == TurboLean.Blake3.blake3Bytes payload)
        let found := match (String.fromUTF8? payload).bind CertifiedRuleBundle.fromJson? with
            | some b => b :: found
            | none => found
        some (offset + size, found)) (start, [])
      if endOffset != bytes.size then none else match bundles with
      | [bundle] => some bundle
      | _ => none
where
  normalizePackJson (s : String) : Option String :=
    -- Manifest booleans/null are irrelevant to bundle offsets; preserve all quoted text.
    go (s.length + 1) s.toList
  go : Nat → List Char → Option String
    | 0, _ => none
    | _ + 1, [] => some ""
    | n + 1, '"' :: rest => do
      let (s, rem) ← StochasticJson.quoted rest
      some (StochasticJson.render (.str s) ++ (← go n rem))
    | n + 1, 't' :: 'r' :: 'u' :: 'e' :: rest
    | n + 1, 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest
    | n + 1, 'n' :: 'u' :: 'l' :: 'l' :: rest => do some ("0" ++ (← go n rest))
    | n + 1, c :: rest => do some (String.singleton c ++ (← go n rest))

def loadStochasticBundleFromPath (path : String) : IO CertifiedRuleBundle := do
  let bytes ← IO.FS.readBinFile path
  let bytes ← if bytes.extract 0 4 == ByteArray.mk #[0x28, 0xB5, 0x2F, 0xFD] then do
      let child ← IO.Process.spawn { cmd := "zstd", args := #["-d", "-c", "--", path], stdout := .piped }
      let mut output := ByteArray.empty
      repeat
        let chunk ← child.stdout.read 65536
        if chunk.isEmpty then break
        output := output ++ chunk
      let exit ← child.wait
      if exit != 0 then throw <| IO.userError "Invalid compressed stochastic bundle"
      pure output
    else pure bytes
  let bundle? := if bytes.extract 0 4 == "TLPK".toUTF8 then decodeStochasticPack? bytes
    else (String.fromUTF8? bytes).bind CertifiedRuleBundle.fromJson?
  let some bundle := bundle? | throw <| IO.userError "Invalid stochastic certificate bundle schema or pack"
  unless bundle.certificates.all (validateCertifiedRewriteCert bundle.profile) do
    throw <| IO.userError "Invalid stochastic rewrite certificate"
  return bundle

def runOptPipelineWithArgs (args : List String) (useVerifiedOnly : Bool) (m : LNIRModule) :
    IO (LNIRModule × List PassStepCert) := do
  let rec bundlePath : List String → Except String (Option String)
    | [] => .ok none
    | "--stochastic-bundle" :: path :: rest => do
      if path.isEmpty || path.startsWith "-" then .error "Missing stochastic bundle path" else
        if (← bundlePath rest).isSome then .error "Duplicate --stochastic-bundle" else .ok (some path)
    | ["--stochastic-bundle"] => .error "Missing stochastic bundle path"
    | _ :: rest => bundlePath rest
  let path ← match bundlePath args with
    | .ok p => pure p
    | .error e => throw <| IO.userError e
  match path with
  | none => return if useVerifiedOnly then runVerifiedKernelPipeline m else runDefaultPipeline m
  | some path =>
    let bundle ← loadStochasticBundleFromPath path
    let pass := mkStochasticCertPass bundle
    return runPassPipeline (if useVerifiedOnly then verifiedKernelPasses ++ [pass] else pass :: defaultPasses) m

structure SuperoptEvolveConfig where
  target : SuperoptTarget := .x86_64
  generations : Nat := defaultEvolveGenerations
  seed : UInt64 := defaultEvolveSeed
  bundleOut : Option String := none
  input : String := "canonical"
  json : Bool := false
  deriving Repr, Inhabited, BEq

private structure ParseState where
  target? : Option SuperoptTarget := none
  generations? : Option Nat := none
  seed? : Option UInt64 := none
  bundleOut? : Option String := none
  input? : Option String := none
  jsonSeen : Bool := false

def parseStrictSuperoptTarget? : String → Option SuperoptTarget
  | "x86_64" => some .x86_64
  | "arm64" => some .arm64
  | "cuda_ptx" => some .cuda_ptx
  | "apple_metal" => some .apple_metal
  | _ => none

def parseStrictDecimalNat? (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty || !cs.all Char.isDigit then none
  else if cs.length > 1 && cs.head? == some '0' then none
  else s.toNat?

def parseStrictU64? (s : String) : Option UInt64 := do
  let n ← parseStrictDecimalNat? s
  if n < 2 ^ 64 then some (UInt64.ofNat n) else none

def parseStrictGenerations? (s : String) : Except String Nat :=
  match parseStrictDecimalNat? s with
  | none => .error s!"[lean-native-core] Invalid --generations '{s}' (expected decimal integer in 0..={maxEvolveGenerations})"
  | some n =>
    if n ≤ maxEvolveGenerations then .ok n
    else .error s!"[lean-native-core] --generations {n} exceeds budget cap ({maxEvolveGenerations})"

private def parseEvolveFlags : List String → ParseState → Except String ParseState
  | [], st => .ok st
  | "--json" :: rest, st =>
    if st.jsonSeen then .error "[lean-native-core] Duplicate flag '--json'"
    else parseEvolveFlags rest { st with jsonSeen := true }
  | f :: [], _ =>
    if ["--target", "--generations", "--seed", "--bundle-out", "--input"].contains f then
      .error s!"[lean-native-core] Flag '{f}' requires a value"
    else
      .error s!"[lean-native-core] Unknown argument '{f}' in superopt-evolve"
  | "--target" :: v :: rest, st =>
    if st.target?.isSome then .error "[lean-native-core] Duplicate flag '--target'"
    else if v.isEmpty || v.startsWith "-" then .error s!"[lean-native-core] Flag '--target' requires a valid value, got '{v}'"
    else
      match parseStrictSuperoptTarget? v with
      | some t => parseEvolveFlags rest { st with target? := some t }
      | none => .error s!"[lean-native-core] Unsupported superopt-evolve target '{v}' (expected x86_64, arm64, cuda_ptx, or apple_metal)"
  | "--generations" :: v :: rest, st =>
    if st.generations?.isSome then .error "[lean-native-core] Duplicate flag '--generations'"
    else if v.isEmpty || v.startsWith "-" then .error s!"[lean-native-core] Flag '--generations' requires a valid value, got '{v}'"
    else do
      let g ← parseStrictGenerations? v
      parseEvolveFlags rest { st with generations? := some g }
  | "--seed" :: v :: rest, st =>
    if st.seed?.isSome then .error "[lean-native-core] Duplicate flag '--seed'"
    else if v.isEmpty || v.startsWith "-" then .error s!"[lean-native-core] Flag '--seed' requires a valid value, got '{v}'"
    else
      match parseStrictU64? v with
      | some sd => parseEvolveFlags rest { st with seed? := some sd }
      | none => .error s!"[lean-native-core] Invalid or out-of-range u64 '--seed' value '{v}'"
  | "--bundle-out" :: v :: rest, st =>
    if st.bundleOut?.isSome then .error "[lean-native-core] Duplicate flag '--bundle-out'"
    else if v.isEmpty || v.startsWith "-" then .error s!"[lean-native-core] Flag '--bundle-out' requires a valid value, got '{v}'"
    else parseEvolveFlags rest { st with bundleOut? := some v }
  | "--input" :: v :: rest, st =>
    if st.input?.isSome then .error "[lean-native-core] Duplicate flag '--input'"
    else if v.isEmpty || v.startsWith "-" then .error s!"[lean-native-core] Flag '--input' requires a valid value, got '{v}'"
    else parseEvolveFlags rest { st with input? := some v }
  | arg :: _ :: _, _ =>
    .error s!"[lean-native-core] Unknown argument '{arg}' in superopt-evolve"

def parseSuperoptEvolveArgs (args : List String) : Except String SuperoptEvolveConfig := do
  let st ← parseEvolveFlags args {}
  return {
    target := st.target?.getD .x86_64
    generations := st.generations?.getD defaultEvolveGenerations
    seed := st.seed?.getD defaultEvolveSeed
    bundleOut := st.bundleOut?
    input := st.input?.getD "canonical"
    json := st.jsonSeen
  }

inductive EvolveInputPayload where
  | module (mod : LNIRModule)
  | candidates (items : List StochasticCandidate)
  deriving Repr, BEq

private def normalizeModuleJson : Nat → List Char → Option String
  | 0, _ => none
  | _ + 1, [] => some ""
  | fuel + 1, '"' :: rest => do
    let (s, remaining) ← StochasticJson.quoted rest
    let suffix ← normalizeModuleJson fuel remaining
    some (StochasticJson.render (.str s) ++ suffix)
  | fuel + 1, 't' :: 'r' :: 'u' :: 'e' :: rest
  | fuel + 1, 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest
  | fuel + 1, 'n' :: 'u' :: 'l' :: 'l' :: rest => do
    let suffix ← normalizeModuleJson fuel rest
    some ("0" ++ suffix)
  | fuel + 1, c :: rest => do
    let suffix ← normalizeModuleJson fuel rest
    some (String.singleton c ++ suffix)

private def checkJsonBalanced : List Char → Bool → Bool → List Char → Bool
  | [], false, false, [] => true
  | [], _, _, _ => false
  | _ :: rest, true, true, stack => checkJsonBalanced rest true false stack
  | '"' :: rest, true, false, stack => checkJsonBalanced rest false false stack
  | '\\' :: rest, true, false, stack => checkJsonBalanced rest true true stack
  | c :: rest, true, false, stack =>
    if c.toNat < 32 then false else checkJsonBalanced rest true false stack
  | '"' :: rest, false, _, stack => checkJsonBalanced rest true false stack
  | '{' :: rest, false, _, stack => checkJsonBalanced rest false false ('}' :: stack)
  | '[' :: rest, false, _, stack => checkJsonBalanced rest false false (']' :: stack)
  | '}' :: rest, false, _, '}' :: stack => checkJsonBalanced rest false false stack
  | ']' :: rest, false, _, ']' :: stack => checkJsonBalanced rest false false stack
  | '}' :: _, false, _, _ => false
  | ']' :: _, false, _, _ => false
  | _ :: rest, false, _, stack => checkJsonBalanced rest false false stack

def decodeStrictModulePayload? (raw : String) : Option LNIRModule :=
  let t := raw.trimAscii.toString
  if t.isEmpty || t == "canonical" || t == "LeanNative.Benchmarks.Canonical" ||
      t == "fastcheck" || t == "LeanNative.FastCheck.Sample" then
    none
  else if t.startsWith "LNIR_WIRE_V1|" then
    LNIRModule.fromWire? t
  else if t.startsWith "{" && t.endsWith "}" && checkJsonBalanced t.toList false false [] then do
    let normalized ← normalizeModuleJson (t.length + 1) t.toList
    let value ← StochasticJson.parse? normalized
    let wire ← StochasticJson.string? (← StochasticJson.field? value "wire")
    if wire.startsWith "LNIR_WIRE_V1|" then LNIRModule.fromWire? wire else none
  else
    none

def validateModuleForEvolve (srcLabel : String) (mod : LNIRModule) : Except String LNIRModule := do
  if mod.decls.isEmpty then
    .error s!"[lean-native-core] Module '{mod.moduleName}' from '{srcLabel}' contains 0 declarations"
  if mod.decls.any (fun d => d.assurance == .unsupported) then
    .error s!"[lean-native-core] Module '{mod.moduleName}' contains unsupported (A_L0) declarations"
  if let some dName := mod.findRcAdtDecl? then
    .error s!"[lean-native-core] Module '{mod.moduleName}' contains RC-ADT declaration '{dName}'"
  return mod

def parseCandidateOrArrayPayload? (raw : String) : Option (List StochasticCandidate) :=
  let t := raw.trimAscii.toString
  if t.startsWith "[" then
    parseExternalCandidates? t
  else if t.startsWith "{" then
    (StochasticCandidate.fromJson? t).map (fun c => [c])
  else
    none

def decodeEvolveRawPayload (srcLabel : String) (raw : String) : Except String EvolveInputPayload :=
  let t := raw.trimAscii.toString
  if t.isEmpty then
    .error s!"[lean-native-core] Empty input file '{srcLabel}'"
  else if let some cands := parseCandidateOrArrayPayload? t then
    .ok (.candidates cands)
  else if let some mod := decodeStrictModulePayload? t then do
    let vmod ← validateModuleForEvolve srcLabel mod
    .ok (.module vmod)
  else
    .error s!"[lean-native-core] Malformed superopt-evolve input '{srcLabel}' (expected LNIR wire/JSON module or StochasticCandidate JSON list)"

def loadEvolveInput (elaborateHook? : Option (String → TargetArch → IO LNIRModule))
    (cfg : SuperoptEvolveConfig) : IO EvolveInputPayload := do
  if cfg.input == "canonical" then
    return .module mkCanonicalBenchmarkModule
  if !(← System.FilePath.pathExists cfg.input) then
    throw <| IO.userError s!"[lean-native-core] Input file '{cfg.input}' does not exist"
  if ← (System.FilePath.mk cfg.input).isDir then
    throw <| IO.userError s!"[lean-native-core] Input path '{cfg.input}' is a directory"
  if cfg.input.endsWith ".lean" then
    let arch : TargetArch := if cfg.target == .arm64 then .arm64 else .x86_64
    match elaborateHook? with
    | some ingestFn =>
      let mod ← ingestFn cfg.input arch
      match validateModuleForEvolve cfg.input mod with
      | .ok vmod => return .module vmod
      | .error msg => throw <| IO.userError msg
    | none =>
      let appPath ← IO.appPath
      let sibBin := appPath.parent.map (· / "lean-native") |>.getD (System.FilePath.mk "lean-native")
      let binToRun ← if ← System.FilePath.pathExists sibBin then pure sibBin.toString else pure "lean-native"
      let out ← IO.Process.output { cmd := binToRun, args := #["emit-lnir", "--wire", "--arch", arch.triple, cfg.input] }
      if out.exitCode != 0 then
        let errDetail := out.stderr.trimAscii.toString
        throw <| IO.userError s!"[lean-native-core] Failed to elaborate '{cfg.input}': {errDetail}"
      match decodeStrictModulePayload? out.stdout with
      | some mod =>
        match validateModuleForEvolve cfg.input mod with
        | .ok vmod => return .module vmod
        | .error msg => throw <| IO.userError msg
      | none =>
        throw <| IO.userError s!"[lean-native-core] Failed to decode elaborated LNIR wire from '{cfg.input}'"
  let raw ← IO.FS.readFile cfg.input
  match decodeEvolveRawPayload cfg.input raw with
  | .ok payload => return payload
  | .error msg => throw <| IO.userError msg

def collectScalarSubexprs : ScalarExpr → List ScalarExpr
  | e@(.constU64 _) | e@(.constBool _) | e@(.var _) => [e]
  | e@(.binOp _ l r) => e :: (collectScalarSubexprs l ++ collectScalarSubexprs r)
  | e@(.unaryOp _ a) => e :: collectScalarSubexprs a
  | e@(.select c t f) => e :: (collectScalarSubexprs c ++ collectScalarSubexprs t ++ collectScalarSubexprs f)
  | e@(.fma a b c) => e :: (collectScalarSubexprs a ++ collectScalarSubexprs b ++ collectScalarSubexprs c)

def collectEvolutionCodeRoots : LNIRCode → List ScalarExpr
  | .letBind _ _ (.scalar e) k => collectScalarSubexprs e ++ collectEvolutionCodeRoots k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k =>
    collectEvolutionCodeRoots k
  | .ite _ t f => collectEvolutionCodeRoots t ++ collectEvolutionCodeRoots f
  | .seqFor _ _ _ _ _ _ step k => collectEvolutionCodeRoots step ++ collectEvolutionCodeRoots k
  | .parFor _ _ _ _ (.customScalar _ _ body) k =>
    collectScalarSubexprs body ++ collectEvolutionCodeRoots k
  | .parFor _ _ _ _ _ k => collectEvolutionCodeRoots k
  | .ret _ | .unreachable => []

def collectEvolutionModuleRoots (m : LNIRModule) : List ScalarExpr :=
  let topRoots := collectModuleScalarRoots m
  let deepRoots := m.decls.flatMap (fun d => collectEvolutionCodeRoots d.body)
  let nonTrivial := (topRoots ++ deepRoots).filter (fun e =>
    match e with
    | .constU64 _ | .constBool _ | .var _ => false
    | _ => true)
  dedupScalarExprs nonTrivial

private def upsertBetterCert (certs : List CertifiedRewriteCert) (c : CertifiedRewriteCert) :
    List CertifiedRewriteCert :=
  match certs.find? (fun ex => ex.candidate.lhs == c.candidate.lhs) with
  | none => certs ++ [c]
  | some ex =>
    if c.costAfter < ex.costAfter then
      certs.map (fun item => if item.candidate.lhs == c.candidate.lhs then c else item)
    else
      certs

def mergeCertifiedRewrites (certs : List CertifiedRewriteCert) : List CertifiedRewriteCert :=
  certs.foldl upsertBetterCert []

structure SuperoptEvolveReceipt where
  inputKind : String
  moduleName : String
  target : SuperoptTarget
  generations : Nat
  seed : UInt64
  rootsCollected : Nat
  externalCandidates : Nat
  rejectedCandidates : Nat
  certCount : Nat
  verifiedRulesCount : Nat
  certCostBefore : Nat
  certCostAfter : Nat
  moduleCostBefore : Nat
  moduleCostAfter : Nat
  bundle : CertifiedRuleBundle
  deriving Repr, BEq

def executeSuperoptEvolve (cfg : SuperoptEvolveConfig) (payload : EvolveInputPayload) : SuperoptEvolveReceipt :=
  let profile := HardwareCostProfile.forTarget cfg.target
  match payload with
  | .module mod =>
    let roots := collectEvolutionModuleRoots mod
    let evolved := evolveBundle profile cfg.generations cfg.seed roots
    let certs := mergeCertifiedRewrites evolved.certificates
    let bundle : CertifiedRuleBundle := {
      profile := profile
      generations := cfg.generations
      seed := cfg.seed
      certificates := certs
    }
    let rules := certBundleToVerifiedRules bundle
    let modCostBefore := mod.decls.foldl (fun acc d => acc + codeScalarCostWithProfile profile d.body) 0
    let optDecls := mod.decls.map (fun d => { d with body := applyCertifiedBundleCode bundle d.body })
    let modCostAfter := optDecls.foldl (fun acc d => acc + codeScalarCostWithProfile profile d.body) 0
    let certBefore := certs.foldl (fun acc c => acc + c.costBefore) 0
    let certAfter := certs.foldl (fun acc c => acc + c.costAfter) 0
    let rejected := roots.length - certs.length
    {
      inputKind := "module"
      moduleName := mod.moduleName
      target := cfg.target
      generations := cfg.generations
      seed := cfg.seed
      rootsCollected := roots.length
      externalCandidates := 0
      rejectedCandidates := rejected
      certCount := certs.length
      verifiedRulesCount := rules.length
      certCostBefore := certBefore
      certCostAfter := certAfter
      moduleCostBefore := modCostBefore
      moduleCostAfter := modCostAfter
      bundle := bundle
    }
  | .candidates extCands =>
    let directCerts := extCands.filterMap (certifyCandidateRule? profile)
    let rejected := extCands.length - directCerts.length
    let roots := dedupScalarExprs (extCands.map (·.lhs))
    let evolved :=
      if cfg.generations == 0 then []
      else (evolveBundle profile cfg.generations cfg.seed roots).certificates
    let certs := mergeCertifiedRewrites (directCerts ++ evolved)
    let bundle : CertifiedRuleBundle := {
      profile := profile
      generations := cfg.generations
      seed := cfg.seed
      certificates := certs
    }
    let rules := certBundleToVerifiedRules bundle
    let certBefore := certs.foldl (fun acc c => acc + c.costBefore) 0
    let certAfter := certs.foldl (fun acc c => acc + c.costAfter) 0
    {
      inputKind := "candidates"
      moduleName := "external_candidates"
      target := cfg.target
      generations := cfg.generations
      seed := cfg.seed
      rootsCollected := roots.length
      externalCandidates := extCands.length
      rejectedCandidates := rejected
      certCount := certs.length
      verifiedRulesCount := rules.length
      certCostBefore := certBefore
      certCostAfter := certAfter
      moduleCostBefore := certBefore
      moduleCostAfter := certAfter
      bundle := bundle
    }

def SuperoptEvolveReceipt.bundleValue (r : SuperoptEvolveReceipt) : StochasticJson.Value :=
  .obj [
    ("schema", .str "lean-native.stochastic-cert.v1"),
    ("profile", StochasticJson.profileValue r.bundle.profile),
    ("generations", .num r.bundle.generations),
    ("seed", .num r.bundle.seed.toNat),
    ("certificates", .arr (r.bundle.certificates.map StochasticJson.certValue))
  ]

def SuperoptEvolveReceipt.toJson (r : SuperoptEvolveReceipt) (bundleOut? : Option String := none) : String :=
  let costSavings := r.certCostBefore - r.certCostAfter
  let modSavings := r.moduleCostBefore - r.moduleCostAfter
  let baseFields : List (String × StochasticJson.Value) := [
    ("schema", .str "lean-native.superopt-evolve-receipt.v1"),
    ("status", .str "evolved"),
    ("target", .str r.target.toString),
    ("profileId", .str r.bundle.profile.profileId),
    ("inputKind", .str r.inputKind),
    ("moduleName", .str r.moduleName),
    ("generations", .num r.generations),
    ("seed", .num r.seed.toNat),
    ("rootsCollected", .num r.rootsCollected),
    ("externalCandidates", .num r.externalCandidates),
    ("acceptedRules", .num r.certCount),
    ("certCount", .num r.certCount),
    ("verifiedRules", .num r.verifiedRulesCount),
    ("rejectedCandidates", .num r.rejectedCandidates),
    ("costBefore", .num r.moduleCostBefore),
    ("costAfter", .num r.moduleCostAfter),
    ("costSavings", .num modSavings),
    ("certCostBefore", .num r.certCostBefore),
    ("certCostAfter", .num r.certCostAfter),
    ("certCostSavings", .num costSavings),
    ("costStats", .obj [
      ("moduleCostBefore", .num r.moduleCostBefore),
      ("moduleCostAfter", .num r.moduleCostAfter),
      ("moduleCostSavings", .num modSavings),
      ("certCostBefore", .num r.certCostBefore),
      ("certCostAfter", .num r.certCostAfter),
      ("certCostSavings", .num costSavings)
    ])
  ]
  let outFields : List (String × StochasticJson.Value) :=
    match bundleOut? with
    | some p => [("bundle_out", .str p)]
    | none => []
  StochasticJson.render (.obj (baseFields ++ outFields ++ [("bundle", r.bundleValue)]))

def SuperoptEvolveReceipt.formatSummary (r : SuperoptEvolveReceipt) (bundleOut? : Option String := none) : String :=
  let outSuffix := match bundleOut? with | some p => s!", bundleOut={p}" | none => ""
  s!"[superopt-evolve] target={r.target.toString}, generations={r.generations}, seed={r.seed}, inputKind={r.inputKind}, roots={r.rootsCollected}, certs={r.certCount}, cost={r.moduleCostBefore}->{r.moduleCostAfter}{outSuffix}"

def runSuperoptEvolve (elaborateHook? : Option (String → TargetArch → IO LNIRModule))
    (args : List String) : IO UInt32 := do
  let cfg ← match parseSuperoptEvolveArgs args with
    | .ok c => pure c
    | .error msg => throw <| IO.userError msg
  if let some outPath := cfg.bundleOut then
    if ← (System.FilePath.mk outPath).isDir then
      throw <| IO.userError s!"[lean-native-core] Bundle output destination is a directory: {outPath}"
  let payload ← loadEvolveInput elaborateHook? cfg
  let receipt := executeSuperoptEvolve cfg payload
  if let some outPath := cfg.bundleOut then
    let outFp := System.FilePath.mk outPath
    if let some parent := outFp.parent then
      if !parent.toString.isEmpty then
        IO.FS.createDirAll parent
    writeTextAtomic outPath receipt.bundle.toJson
  if cfg.json then
    IO.println (receipt.toJson cfg.bundleOut)
  else
    IO.println (receipt.formatSummary cfg.bundleOut)
  return 0

end LeanNative.Driver.CoreCLI
