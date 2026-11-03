import LeanNative.Backend.MetalLower
import LeanNative.Backend.MetalAst
import LeanNative.Semantics.Eval

/-!
# LNIR-to-Metal Specification Bridges (`LeanNative.Proofs.MetalLowerSpec`)

Specification-only bridges connecting `LeanNative.Semantics.Eval` environments and heap
buffers to `MetalAst` local register bindings and device `ByteMemory` buffers, kept in
`LeanNative.Proofs.*` so `LeanNative.Backend.MetalLower` has zero imports from
`LeanNative.Semantics.*`.
-/

namespace LeanNative.Proofs.MetalLowerSpec

open LeanNative.IR
open LeanNative.Semantics
open LeanNative.Backend

def valOfSort (s : Bool) : Val → Option (BitVec 64)
  | .u64 x => if !s then some x.toBitVec else none
  | .bool b => if s then some (if b then 1#64 else 0#64) else none
  | _ => none

def valToU64Bv : Val → Option (BitVec 64)
  | .u64 x => some x.toBitVec
  | .bool b => some (if b then 1#64 else 0#64)
  | _ => none

def varEnvMatchesLocals (env : VarEnv) (ls : MetalAst.MSLLocals) (idxName : String)
    (idxVar : Nat) : List Nat → Prop
  | [] => True
  | id :: rest =>
    (∃ x : UInt64, env id = some (.u64 x) ∧
      ls.lookup? (if id == idxVar then idxName else s!"v{id}") = some x.toBitVec ∧
      ls.lookupType? (if id == idxVar then idxName else s!"v{id}") = some .ulong) ∧
    varEnvMatchesLocals env ls idxName idxVar rest

def packOneDeviceBuffer (env : VarEnv) (st : HeapState) (len : Nat) (v : VarId) :
    Option MetalAst.ByteMemory :=
  match env v with
  | some (.sarrayId bid) | some (.rawPtrId bid) =>
    match st.findBuffer bid with
    | some buf =>
      if len ≤ buf.data.size then
        some (MetalAst.ByteMemory.ofU64Words
          ((List.range len).map fun i => (buf.data[i]?.getD 0).toBitVec))
      else none
    | none => none
  | _ => none

def indexDeviceBuffers : Nat → List MetalAst.ByteMemory → List (Nat × MetalAst.ByteMemory)
  | _, [] => []
  | idx, m :: ms => (idx, m) :: indexDeviceBuffers (idx + 1) ms

def packInputDeviceBuffersGo (env : VarEnv) (st : HeapState) (len : Nat) (idx : Nat)
    (inputs : List VarId) : Option (List (Nat × MetalAst.ByteMemory)) :=
  (inputs.mapM (packOneDeviceBuffer env st len)).map (indexDeviceBuffers idx)

def packInputDeviceBuffers (env : VarEnv) (st : HeapState) (inputs : List VarId) (len : Nat) :
    Option (List (Nat × MetalAst.ByteMemory)) :=
  packInputDeviceBuffersGo env st len 0 inputs

theorem packInputDeviceBuffersGo_nil (env : VarEnv) (st : HeapState) (len idx : Nat) :
    packInputDeviceBuffersGo env st len idx [] = some [] := rfl

theorem packInputDeviceBuffersGo_cons (env : VarEnv) (st : HeapState) (len idx : Nat)
    (v : VarId) (rest : List VarId) :
    packInputDeviceBuffersGo env st len idx (v :: rest) =
      match packOneDeviceBuffer env st len v with
      | none => none
      | some m =>
        match packInputDeviceBuffersGo env st len (idx + 1) rest with
        | none => none
        | some tail => some ((idx, m) :: tail) := by
  simp only [packInputDeviceBuffersGo, List.mapM_cons]
  cases packOneDeviceBuffer env st len v with
  | none => rfl
  | some m =>
    cases List.mapM (packOneDeviceBuffer env st len) rest with
    | none => rfl
    | some ms => rfl

end LeanNative.Proofs.MetalLowerSpec
