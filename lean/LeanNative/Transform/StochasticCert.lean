import LeanNative.IR.Codec
import LeanNative.Proofs.SuperoptSoundness
import LeanNative.Transform.LoopSchedule

namespace LeanNative.Transform

open LeanNative.IR LeanNative.Semantics LeanNative.Proofs

set_option autoImplicit false

structure StochasticCandidate where
  lhs : ScalarExpr
  rhs : ScalarExpr
  deriving Repr, Inhabited, BEq

structure CertifiedRewriteCert where
  candidate : StochasticCandidate
  costBefore : Nat
  costAfter : Nat
  theoremRef : String := "LeanNative.Proofs.certifyScalarPair_sound"
  deriving Repr, Inhabited, BEq

structure CertifiedRuleBundle where
  profile : HardwareCostProfile
  generations : Nat
  seed : UInt64
  certificates : List CertifiedRewriteCert
  deriving Repr, Inhabited, BEq

abbrev exprCost (profile : HardwareCostProfile) (e : ScalarExpr) : Nat :=
  scalarExprCostWithProfile profile e

def certifyScalarPair (profile : HardwareCostProfile) (lhs rhs : ScalarExpr) : Bool :=
  fastCheckScalarEquiv lhs rhs && checkSuperoptScalarVerified lhs rhs &&
    decide (exprCost profile rhs < exprCost profile lhs)

def certifyCandidateRule? (profile : HardwareCostProfile) (candidate : StochasticCandidate) :
    Option CertifiedRewriteCert :=
  if certifyScalarPair profile candidate.lhs candidate.rhs then
    some {
      candidate := candidate
      costBefore := scalarExprCostWithProfile profile candidate.lhs
      costAfter := scalarExprCostWithProfile profile candidate.rhs }
  else none

def applyCertifiedScalarRewrite (profile : HardwareCostProfile) (candidate : StochasticCandidate)
    (e : LNIRExpr) : LNIRExpr :=
  match e with
  | .scalar lhs =>
    if lhs == candidate.lhs && certifyScalarPair profile candidate.lhs candidate.rhs then
      .scalar candidate.rhs
    else e
  | _ => e

def candidateToVerifiedRule (profile : HardwareCostProfile) (candidate : StochasticCandidate) :
    VerifiedExprRule where
  name := "StochasticCert:" ++ hashStringFNV64 (reprStr candidate)
  apply := applyCertifiedScalarRewrite profile candidate
  sound := by
    intro e
    cases e with
    | scalar lhs =>
      unfold applyCertifiedScalarRewrite
      dsimp only
      split
      · rename_i h
        simp only [certifyScalarPair, Bool.and_eq_true] at h
        rcases h with ⟨heq, ⟨_, hver⟩, _⟩
        have hlhs := ScalarExpr_eq_of_beq heq
        subst lhs
        exact checkSuperoptScalarVerified_sound _ _ hver
      · exact ExprRefines.refl _
    | constU256 _ | mulDivDown _ _ _ | mulDivUp _ _ _ | storageLoad _ _ | storageStore _ _ _
    | mkTuple _ | projTuple _ _ | allocCtor _ _ _ | ctorGetObj _ _ | ctorGetScalar _ _ _
    | isExclusive _ | sarrayLen _ | sarrayDataPtr _ _ | sarrayEnsureExclusive _ _
    | sarrayGet _ _ _ | sarraySet _ _ _ _ | rawLoad _ _ _ | boxScalar _ _ | unboxScalar _ _
    | call _ _ _ _ => exact ExprRefines.refl _

def validateCertifiedRewriteCert (profile : HardwareCostProfile) (cert : CertifiedRewriteCert) : Bool :=
    cert.costBefore == scalarExprCostWithProfile profile cert.candidate.lhs &&
        cert.costAfter == scalarExprCostWithProfile profile cert.candidate.rhs &&
        cert.theoremRef == "LeanNative.Proofs.certifyScalarPair_sound" &&
        certifyScalarPair profile cert.candidate.lhs cert.candidate.rhs

def certBundleToVerifiedRules (bundle : CertifiedRuleBundle) : List VerifiedExprRule :=
  bundle.certificates.filterMap fun cert =>
    if validateCertifiedRewriteCert bundle.profile cert then
      some (candidateToVerifiedRule bundle.profile cert.candidate)
    else none

def applyCertToScalar (profile : HardwareCostProfile) (e : ScalarExpr)
    (cert : CertifiedRewriteCert) : ScalarExpr :=
  if e == cert.candidate.lhs && validateCertifiedRewriteCert profile cert then cert.candidate.rhs else e

def applyCertsToScalar (profile : HardwareCostProfile) (certs : List CertifiedRewriteCert) :
    ScalarExpr → ScalarExpr
  | .binOp op l r => certs.foldl (applyCertToScalar profile)
      (.binOp op (applyCertsToScalar profile certs l) (applyCertsToScalar profile certs r))
  | .unaryOp op a => certs.foldl (applyCertToScalar profile) (.unaryOp op (applyCertsToScalar profile certs a))
  | .select c t f => certs.foldl (applyCertToScalar profile)
      (.select (applyCertsToScalar profile certs c) (applyCertsToScalar profile certs t) (applyCertsToScalar profile certs f))
  | .fma a b c => certs.foldl (applyCertToScalar profile)
      (.fma (applyCertsToScalar profile certs a) (applyCertsToScalar profile certs b) (applyCertsToScalar profile certs c))
  | leaf => certs.foldl (applyCertToScalar profile) leaf

def applyCertifiedBundleCode (bundle : CertifiedRuleBundle) : LNIRCode → LNIRCode
  | .letBind dst ty (.scalar e) k =>
    .letBind dst ty (.scalar (applyCertsToScalar bundle.profile bundle.certificates e)) (applyCertifiedBundleCode bundle k)
  | .letBind dst ty e k => .letBind dst ty e (applyCertifiedBundleCode bundle k)
  | .rawStore pv iv vv ty k => .rawStore pv iv vv ty (applyCertifiedBundleCode bundle k)
  | .incRef v n k => .incRef v n (applyCertifiedBundleCode bundle k)
  | .decRef v n k => .decRef v n (applyCertifiedBundleCode bundle k)
  | .ite v t f => .ite v (applyCertifiedBundleCode bundle t) (applyCertifiedBundleCode bundle f)
  | .seqFor iv lv hv av ai ty step k =>
    .seqFor iv lv hv av ai ty (applyCertifiedBundleCode bundle step) (applyCertifiedBundleCode bundle k)
  | .parFor ov lv ins ty (.customScalar iv vs body) k =>
    .parFor ov lv ins ty (.customScalar iv vs (applyCertsToScalar bundle.profile bundle.certificates body))
      (applyCertifiedBundleCode bundle k)
  | .parFor ov lv ins ty kernel k => .parFor ov lv ins ty kernel (applyCertifiedBundleCode bundle k)
  | .ret v => .ret v
  | .unreachable => .unreachable

def evalWithStochasticProposer (profile : HardwareCostProfile)
    (proposer : ScalarExpr → Option ScalarExpr) (lhs : ScalarExpr) : ScalarExpr :=
  match proposer lhs with
  | none => lhs
  | some rhs => if certifyScalarPair profile lhs rhs then rhs else lhs

def mutateScalar (seed : UInt64) (e : ScalarExpr) : ScalarExpr :=
  let r := (splitMix64Next seed).1
  match e with
  | .binOp op l rhs =>
    match r.toNat % 5 with
    | 0 => l
    | 1 => rhs
    | 2 => .binOp op rhs l
    | 3 => .binOp op l (.constU64 (r % 65))
    | _ => rewriteScalarVerified e
  | .unaryOp _ a => if r % 2 == 0 then a else rewriteScalarVerified e
  | .select _ t f => if r % 2 == 0 then t else f
  | .fma a b c => if r % 2 == 0 then .binOp .add (.binOp .mul a b) c else a
  | .constU64 n => .constU64 (n ^^^ (r % 64))
  | .constBool b => .constBool (!b)
  | .var v => .binOp .add (.var v) (.constU64 (r % 2))

def evolveScalar (profile : HardwareCostProfile) : Nat → UInt64 → ScalarExpr → ScalarExpr
  | 0, _, e => e
  | n + 1, seed, e =>
    let (r, next) := splitMix64Next seed
    let candidates := mutateScalar r e :: synthesizeCandidates profile.target e
    let best := candidates.foldl (fun best rhs =>
      if certifyScalarPair profile best rhs then rhs else best) e
    evolveScalar profile n next best

def evolveBundle (profile : HardwareCostProfile) (generations : Nat) (seed : UInt64)
    (roots : List ScalarExpr) : CertifiedRuleBundle :=
  let certificates := roots.zipIdx |>.filterMap fun (lhs, i) =>
    let rhs := evolveScalar profile generations (seed + i.toUInt64) lhs
    certifyCandidateRule? profile { lhs := lhs, rhs := rhs }
  { profile := profile, generations := generations, seed := seed, certificates := certificates }

def collectCodeScalarRoots : LNIRCode → List ScalarExpr
  | .letBind _ _ (.scalar e) k => e :: collectCodeScalarRoots k
  | .letBind _ _ _ k | .rawStore _ _ _ _ k | .incRef _ _ k | .decRef _ _ k =>
    collectCodeScalarRoots k
  | .ite _ t f | .seqFor _ _ _ _ _ _ t f => collectCodeScalarRoots t ++ collectCodeScalarRoots f
  | .parFor _ _ _ _ (.customScalar _ _ e) k => e :: collectCodeScalarRoots k
  | .parFor _ _ _ _ _ k => collectCodeScalarRoots k
  | .ret _ | .unreachable => []

def collectDeclScalarRoots (decl : LNIRDecl) : List ScalarExpr := collectCodeScalarRoots decl.body

def collectModuleScalarRoots (m : LNIRModule) : List ScalarExpr := m.decls.flatMap collectDeclScalarRoots

def proposeLoopSchedule (seed : UInt64) : LoopScheduleSpec :=
  let r := (splitMix64Next seed).1
  { tileSize := 1 + r.toNat % 32, unrollFactor := 1 + (r >>> 8).toNat % 8,
    optimizeStepBody := r % 2 == 0 }

def applyStochasticLoopSchedule (sched : LoopScheduleSpec) (code : LNIRCode) : LNIRCode :=
  if LeanNative.Transform.verifyLoopScheduleLegality sched code then
    LeanNative.Transform.applyLoopSchedule sched code
  else code

namespace StochasticJson

inductive Value where
  | str : String → Value
  | num : Nat → Value
  | arr : List Value → Value
  | obj : List (String × Value) → Value
  deriving Repr, BEq

mutual
  def render : Value → String
    | .str s => jsonStr s
    | .num n => toString n
    | .arr xs => "[" ++ renderList xs ++ "]"
    | .obj xs => "{" ++ renderFields xs ++ "}"

  def renderList : List Value → String
    | [] => ""
    | [x] => render x
    | x :: xs => render x ++ "," ++ renderList xs

  def renderFields : List (String × Value) → String
    | [] => ""
    | [(k, v)] => jsonStr k ++ ":" ++ render v
    | (k, v) :: xs => jsonStr k ++ ":" ++ render v ++ "," ++ renderFields xs
end

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def quoted : List Char → Option (String × List Char)
  | [] => none
  | '"' :: rest => some ("", rest)
  | '\\' :: '"' :: rest => do
    let (s, rem) ← quoted rest
    some ("\"" ++ s, rem)
  | '\\' :: '\\' :: rest => do
    let (s, rem) ← quoted rest
    some ("\\" ++ s, rem)
  | '\\' :: '/' :: rest => do
    let (s, rem) ← quoted rest
    some ("/" ++ s, rem)
  | '\\' :: 'n' :: rest => do
    let (s, rem) ← quoted rest
    some ("\n" ++ s, rem)
  | '\\' :: 'r' :: rest => do
    let (s, rem) ← quoted rest
    some ("\r" ++ s, rem)
  | '\\' :: 't' :: rest => do
    let (s, rem) ← quoted rest
    some ("\t" ++ s, rem)
  | '\\' :: 'b' :: rest => do
    let (s, rem) ← quoted rest
    some (String.singleton (Char.ofNat 8) ++ s, rem)
  | '\\' :: 'f' :: rest => do
    let (s, rem) ← quoted rest
    some (String.singleton (Char.ofNat 12) ++ s, rem)
  | '\\' :: 'u' :: a :: b :: d :: e :: rest => do
    let n := (← hexDigit? a) * 4096 + (← hexDigit? b) * 256 +
      (← hexDigit? d) * 16 + (← hexDigit? e)
    if 0xD800 ≤ n && n ≤ 0xDFFF then none else
      let (s, rem) ← quoted rest
      some (String.singleton (Char.ofNat n) ++ s, rem)
  | '\\' :: _ => none
  | c :: rest => do
    if c.toNat < 32 then none else
      let (s, rem) ← quoted rest
      some (String.singleton c ++ s, rem)

def ws (xs : List Char) : List Char := xs.dropWhile (fun c => c == ' ' || c == '\n' || c == '\r' || c == '\t')

mutual
  def parseValue : Nat → List Char → Option (Value × List Char)
    | 0, _ => none
    | n + 1, xs =>
      match ws xs with
      | '"' :: rest => do
        let (s, rem) ← quoted rest
        some (.str s, rem)
      | '[' :: rest => do
        let (items, rem) ← parseArray n rest
        some (.arr items, rem)
      | '{' :: rest => do
        let (items, rem) ← parseObject n rest
        some (.obj items, rem)
      | rest => do
        let digits := rest.takeWhile Char.isDigit
        let num ← (String.ofList digits).toNat?
        if digits.length > 1 && digits.head? == some '0' then none
        else some (.num num, rest.drop digits.length)

  def parseArray : Nat → List Char → Option (List Value × List Char)
    | 0, _ => none
    | n + 1, xs =>
      if (ws xs).head? == some ']' then some ([], (ws xs).drop 1)
      else do
        let (v, rem) ← parseValue n xs
        match ws rem with
        | ']' :: tail => some ([v], tail)
        | ',' :: tail => do
          if (ws tail).head? == some ']' then none else
            let (vs, last) ← parseArray n tail
            some (v :: vs, last)
        | _ => none

  def parseObject : Nat → List Char → Option (List (String × Value) × List Char)
    | 0, _ => none
    | n + 1, xs =>
      match ws xs with
      | '}' :: tail => some ([], tail)
      | '"' :: tail => do
        let (key, rem) ← quoted tail
        match ws rem with
        | ':' :: rest => do
          let (v, last) ← parseValue n rest
          match ws last with
          | '}' :: final => some ([(key, v)], final)
          | ',' :: final => do
            if (ws final).head? == some '}' then none else
              let (vs, endChars) ← parseObject n final
              if vs.any (fun p => p.1 == key) then none else some ((key, v) :: vs, endChars)
          | _ => none
        | _ => none
      | _ => none
end

def parse? (s : String) : Option Value := do
  let (v, rem) ← parseValue (s.toList.length + 1) s.toList
  if (ws rem).isEmpty then some v else none

def field? (v : Value) (key : String) : Option Value :=
  match v with
  | .obj fields => (fields.find? (fun p => p.1 == key)).map Prod.snd
  | _ => none

def string? : Value → Option String | .str s => some s | _ => none

def nat? : Value → Option Nat | .num n => some n | _ => none

def array? : Value → Option (List Value) | .arr xs => some xs | _ => none

def scalarValue (e : ScalarExpr) : Value :=
  .str (LNIRModule.toWire { moduleName := "scalar", decls :=
    [{ name := "scalar", params := [], retTy := .i64, body := .letBind 0 .i64 (.scalar e) (.ret 0) }] })

def scalar? (v : Value) : Option ScalarExpr := do
  let m ← LNIRModule.fromWire? (← string? v)
  match m.decls with
  | [{ body := .letBind 0 .i64 (.scalar e) (.ret 0), .. }] => some e
  | _ => none

def candidateValue (c : StochasticCandidate) : Value :=
  .obj [("lhs", scalarValue c.lhs), ("rhs", scalarValue c.rhs)]

def candidate? (v : Value) : Option StochasticCandidate := do
  some { lhs := (← scalar? (← field? v "lhs")), rhs := (← scalar? (← field? v "rhs")) }

def profileValue (p : HardwareCostProfile) : Value :=
  .obj [("id", .str p.profileId), ("target", .str p.target.toString),
    ("cpu", .str p.llvmTargetCpu), ("sm", .str p.smArch),
    ("costs", .arr ([p.addSubCost, p.bitwiseCost, p.shiftCost, p.cmpCost, p.mulCost,
      p.divModCost, p.fmaCost, p.selectCost, p.clz256Cost, p.addSubChecked256Cost,
      p.mulChecked256Cost, p.minGpuElements, p.gpuBlockThreads, p.matmulTileDim].map Value.num))]

def profile? (v : Value) : Option HardwareCostProfile := do
  let profileId ← string? (← field? v "id")
  let target ← match (← string? (← field? v "target")) with
    | "x86_64" => some SuperoptTarget.x86_64
    | "arm64" => some .arm64
    | "cuda_ptx" => some .cuda_ptx
    | "apple_metal" => some .apple_metal
    | _ => none
  let llvmTargetCpu ← string? (← field? v "cpu")
  let smArch ← string? (← field? v "sm")
  let costs ← (← array? (← field? v "costs")).mapM nat?
  match costs with
  | [a, b, s, c, m, d, f, sel, clz, ac, mc, minG, block, tile] =>
    some {
      profileId := profileId
      target := target
      llvmTargetCpu := llvmTargetCpu
      smArch := smArch
      addSubCost := a
      bitwiseCost := b
      shiftCost := s
      cmpCost := c
      mulCost := m
      divModCost := d
      fmaCost := f
      selectCost := sel
      clz256Cost := clz
      addSubChecked256Cost := ac
      mulChecked256Cost := mc
      minGpuElements := minG
      gpuBlockThreads := block
      matmulTileDim := tile }
  | _ => none

def certValue (c : CertifiedRewriteCert) : Value :=
  .obj [("candidate", candidateValue c.candidate), ("costBefore", .num c.costBefore),
    ("costAfter", .num c.costAfter), ("theoremRef", .str c.theoremRef)]

def cert? (v : Value) : Option CertifiedRewriteCert := do
  let cand ← candidate? (← field? v "candidate")
  let costBefore ← nat? (← field? v "costBefore")
  let costAfter ← nat? (← field? v "costAfter")
  let theoremRef ← string? (← field? v "theoremRef")
  some {
    candidate := cand
    costBefore := costBefore
    costAfter := costAfter
    theoremRef := theoremRef }

end StochasticJson

def StochasticCandidate.toJson (c : StochasticCandidate) : String :=
  StochasticJson.render (StochasticJson.candidateValue c)

def StochasticCandidate.fromJson? (s : String) : Option StochasticCandidate := do
  StochasticJson.candidate? (← StochasticJson.parse? s)

def CertifiedRewriteCert.toJson (c : CertifiedRewriteCert) : String :=
  StochasticJson.render (StochasticJson.certValue c)

def CertifiedRewriteCert.fromJson? (s : String) : Option CertifiedRewriteCert := do
  StochasticJson.cert? (← StochasticJson.parse? s)

def CertifiedRuleBundle.toJson (b : CertifiedRuleBundle) : String :=
  StochasticJson.render (.obj [("schema", .str "lean-native.stochastic-cert.v1"),
    ("profile", StochasticJson.profileValue b.profile), ("generations", .num b.generations),
    ("seed", .num b.seed.toNat), ("certificates", .arr (b.certificates.map StochasticJson.certValue))])

def CertifiedRuleBundle.fromJson? (s : String) : Option CertifiedRuleBundle := do
  let v ← StochasticJson.parse? s
  let schema ← StochasticJson.string? (← StochasticJson.field? v "schema")
  if schema != "lean-native.stochastic-cert.v1" then none else
    let profile ← StochasticJson.profile? (← StochasticJson.field? v "profile")
    let generations ← StochasticJson.nat? (← StochasticJson.field? v "generations")
    let seed ← StochasticJson.nat? (← StochasticJson.field? v "seed")
    if seed ≥ 2 ^ 64 then none else
      let certificates ← (← StochasticJson.array? (← StochasticJson.field? v "certificates")).mapM StochasticJson.cert?
      some {
        profile := profile
        generations := generations
        seed := seed.toUInt64
        certificates := certificates }

def parseExternalCandidates? (s : String) : Option (List StochasticCandidate) := do
  (← StochasticJson.array? (← StochasticJson.parse? s)).mapM StochasticJson.candidate?

def certifyExternalCandidates? (profile : HardwareCostProfile) (s : String) :
    Option (List CertifiedRewriteCert) := do
  some ((← parseExternalCandidates? s).filterMap (certifyCandidateRule? profile))

def stochasticCertWitnessLhs : ScalarExpr := .binOp .add (.var 0) (.constU64 0)

def stochasticCertWitnessCode : LNIRCode := .letBind 1 .i64 (.scalar stochasticCertWitnessLhs) (.ret 1)

def cachedStochasticBundle : CertifiedRuleBundle :=
  { profile := HardwareCostProfile.forTarget .x86_64
    generations := 1
    seed := 0
    certificates := [{
      candidate := { lhs := stochasticCertWitnessLhs, rhs := .var 0 }
      costBefore := 1
      costAfter := 0 }] }

def cachedStochasticRules : List VerifiedExprRule := certBundleToVerifiedRules cachedStochasticBundle

end LeanNative.Transform
