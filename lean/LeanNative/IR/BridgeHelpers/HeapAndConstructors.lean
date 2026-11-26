import LeanNative.IR.BridgeHelpers.ScalarDagAndJoinPoints

set_option autoImplicit true

namespace LeanNative.IR

open Lean
open Lean.Compiler.LCNF

export LeanNative.IR.RealLCNFBridge (
  lowerScalarIntrinsicExpr? lowerBoolBinIntrinsic? lowerUnaryScalarIntrinsic?
)

/-!
L1 (`roadmap/HORIZONS.md` rung L1, w-l1): the `BridgeM` constructor/heap lowering that lived
here (`lowerTupleOrEnumCtor`, `lowerTupleProj`, `lowerTuplePatternAlt`, `lowerOsetInstr`,
`withActiveCtor`, `withActiveCtor?`, `heapCtorLayoutOfM`, `lowerScalarProjM`,
`lowerRcCtorWithScalarsM`, `lowerScalarSetM`, `lowerSetTagM`, `lowerDelM`) was the deleted
second lowering's heap path; the proved path has its own pure heap lowering in
`RealLCNFBridge.lean`. What stays is the C1.2 constructor pre-pass the driver feeds into
`buildRealBridgeCtxM`.
-/

/-- One round of the C1.2 ctor pre-pass over impure LCNF. `ctx` holds the fvars whose ctor is known at this
    point (`let x := ctor`, a `cases` alt's scrutinee, a known join-point param); each `jmp` records, per
    join-point param, the ctor of every non-erased argument (`none` = unknown). -/
partial def collectJmpArgCtors (known : Std.HashMap Lean.FVarId Lean.Name) (ctx : Std.HashMap Lean.FVarId Lean.Name)
    (jpParams : Std.HashMap Lean.FVarId (Array Lean.FVarId))
    (acc : Std.HashMap Lean.FVarId (List (Option Lean.Name))) :
    Lean.Compiler.LCNF.Code .impure → Std.HashMap Lean.FVarId (List (Option Lean.Name))
  | .let decl k =>
    let ctx' := match decl.value with
      | .ctor info _ _ => ctx.insert decl.fvarId info.name
      | _ => ctx
    collectJmpArgCtors known ctx' jpParams acc k
  | .jp decl k =>
    let jpParams' := jpParams.insert decl.fvarId (decl.params.map (·.fvarId))
    let ctxJp := decl.params.foldl (fun c p => match known[p.fvarId]? with | some n => c.insert p.fvarId n | none => c) ctx
    let acc' := collectJmpArgCtors known ctxJp jpParams' acc decl.value
    collectJmpArgCtors known ctx jpParams' acc' k
  | .jmp fvarId args =>
    match jpParams[fvarId]? with
    | some ps =>
      (ps.toList.zip args.toList).foldl (fun a (p, arg) =>
        match arg with
        | .erased => a
        | .fvar x => a.insert p (ctx[x]? :: a.getD p [])
        | _ => a.insert p (none :: a.getD p [])) acc
    | none => acc
  | .cases c =>
    c.alts.foldl (fun a alt =>
      match alt with
      | .ctorAlt info code _ => collectJmpArgCtors known (ctx.insert c.discr info.name) jpParams a code
      | _ => collectJmpArgCtors known ctx jpParams a alt.getCode) acc
  | .setTag x _ k _ => collectJmpArgCtors known (ctx.erase x) jpParams acc k
  | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ => collectJmpArgCtors known ctx jpParams acc k
  | .return _ | .unreach _ => acc

/-- `let x := ctor` binders anywhere in the body (fvars are unique, so this is scope-independent). -/
partial def collectLetCtors (acc : Std.HashMap Lean.FVarId Lean.Name) : Lean.Compiler.LCNF.Code .impure → Std.HashMap Lean.FVarId Lean.Name
  | .let decl k =>
    collectLetCtors (match decl.value with | .ctor info _ _ => acc.insert decl.fvarId info.name | _ => acc) k
  | .jp decl k => collectLetCtors (collectLetCtors acc decl.value) k
  | .cases c => c.alts.foldl (fun a alt => collectLetCtors a alt.getCode) acc
  | .fun _ k _ | .inc _ _ _ _ k _ | .dec _ _ _ _ _ k _ | .del _ k _ | .oset _ _ _ k _ | .uset _ _ _ k _
  | .sset _ _ _ _ _ k _ | .setTag _ _ k _ => collectLetCtors acc k
  | .jmp .. | .return _ | .unreach _ => acc

/-- C1.2 ctor pre-pass: a join-point param's ctor is known iff every non-erased `jmp` argument has the same
    known ctor (fixpoint over nested reset/reuse join points). Anything else stays unknown (fail closed). -/
def collectFVarCtors (code : Lean.Compiler.LCNF.Code .impure) : Std.HashMap Lean.FVarId Lean.Name := Id.run do
  let lets := collectLetCtors {} code
  let mut known : Std.HashMap Lean.FVarId Lean.Name := {}
  for _ in [0:8] do
    let obs := collectJmpArgCtors known {} {} {} code
    let next := obs.fold (fun m p vs =>
      match vs with
      | some n :: rest => if rest.all (· == some n) then m.insert p n else m
      | _ => m) ({} : Std.HashMap Lean.FVarId Lean.Name)
    if next.size == known.size then break
    known := next
  return lets.fold (fun m k v => m.insert k v) known

end LeanNative.IR
