import LeanNative.Semantics.Value

/-! Shadow-semantics fixture (helper module, NOT inventoried; imports ONLY `LeanNative.Semantics.Value`,
NOT `LeanNative.Semantics.Eval`):
1. `unaryOpaqueCopy`: verbatim `opaque` copy of `LeanNative.Semantics.evalUnaryOp` (stored as `.opaqueInfo`).
2. `varListPartialCopy`: verbatim recursive `partial def` copy of `LeanNative.Semantics.evalVarList`
   (public constant is `.opaqueInfo` `Inhabited.default`; real body lives only in `varListPartialCopy._unsafe_rec`,
   matched against `evalVarList._unsafe_rec`).
3. `seqLoopOpaqueCopy`: verbatim computable recursive `opaque` copy of `LeanNative.Semantics.evalSeqLoop`.
4. `seqLoopNoncompOpaqueCopy`: verbatim recursive `noncomputable opaque` copy of
   `LeanNative.Semantics.evalSeqLoop` (stored ONLY as `.opaqueInfo` + `._f`, with NO `_unsafe_rec`).
None of these helpers mentions any `LeanNative.Semantics.eval*` constant or auxiliary. -/

namespace UnrelatedOpaqueUtil
open LeanNative.IR LeanNative.Semantics

opaque unaryOpaqueCopy (op : UnaryOp) (v : Val) : Except UBError Val :=
  match op, v with
  | .not, .bool b   => .ok (.bool (!b))
  | .not, .u64 n    => .ok (.u64 (~~~n))
  | .not, .u256 w   => .ok (.u256 (UInt256.bitNot w))
  | .neg, .u64 n    => .ok (.u64 (0 - n))
  | .neg, .u256 w   => .ok (.u256 (UInt256.sub UInt256.zero w))
  | .clz256, .u256 w => .ok (.u256 (UInt256.clz w))
  | .clz256, .u64 n  => .ok (.u256 (UInt256.clz (UInt256.ofUInt64 n)))
  | _, _ => .error (.typeError "evalUnaryOp: invalid operand type")

partial def varListPartialCopy (env : VarEnv) (xs : List VarId) : Except UBError (List Val) :=
  match xs with
  | [] => .ok []
  | x :: xs =>
    match env x, varListPartialCopy env xs with
    | some v, .ok vs => .ok (v :: vs)
    | none, _ => .error (.unboundVar x)
    | some _, .error err => .error err

opaque seqLoopOpaqueCopy (count : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (evalStep : VarEnv → HeapState → Except UBError (Val × HeapState)) :
    Except UBError (Val × HeapState) :=
  match count with
  | 0 => .ok (accVal, st)
  | count' + 1 =>
    let stepEnv := (env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal
    match evalStep stepEnv st with
    | .ok (nextAcc, st') =>
      seqLoopOpaqueCopy count' (curIdx + 1) idxVar accVar nextAcc env st' evalStep
    | .error err => .error err

noncomputable opaque seqLoopNoncompOpaqueCopy (count : Nat) (curIdx : Nat) (idxVar accVar : VarId)
    (accVal : Val) (env : VarEnv) (st : HeapState)
    (evalStep : VarEnv → HeapState → Except UBError (Val × HeapState)) :
    Except UBError (Val × HeapState) :=
  match count with
  | 0 => .ok (accVal, st)
  | count' + 1 =>
    let stepEnv := (env.bind idxVar (.u64 curIdx.toUInt64)).bind accVar accVal
    match evalStep stepEnv st with
    | .ok (nextAcc, st') =>
      seqLoopNoncompOpaqueCopy count' (curIdx + 1) idxVar accVar nextAcc env st' evalStep
    | .error err => .error err

end UnrelatedOpaqueUtil
