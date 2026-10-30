# D1 decision (quorum round 2, unanimous Astra + Fable; carbon-4 recused) — 2026-10-30
Option 5: contract-first + one unified PR from #280's base.

Order (Boss enforces): #286 (extracted fixes) merges first → 5a contract PR → 5b unified PR → close #277/#280 with
co-author credit (only after 5b merges).

5a — docs/HEAPOBJ_CONTRACT.md + executable invariants, NO model/emitter change:
- Contract: HeapObj layout {tag, objFields, scalarFields} indexing (mirrors IR `allocCtor tag objFields scalarFields`
  and Lean runtime lean_ctor_get vs lean_ctor_get_uint64), tagged immediates, owning-edge multiplicity (repeated
  owning edges to one child), ctor_set requires rc==1 else UB, decRef is total-or-error (fuel exhaustion = error,
  never partial ok), SymbolicTV must report passed=false on any RC/fuel exhaustion.
- Regressions (#guard / #guard_msgs), with currently-failing ones marked EXPLICIT xfail (not skipped):
  P-cert C3 reproducer (100 owning edges to one child ⇒ decRef returns error, never ok with rc=65);
  underfueled helper on #280's path; repeated owning edges; tagged immediates; scalar-slot indexing; shared ctor_set UB.
5b — unified PR from #280's branch:
- switch HeapObj to the contract's objFields/scalarFields model; import #277's `--allow-rc-adt` opt-in +
  `findRcAdtDecl?` fail-closed gates in every codegen/plugin/worker/binding path + getCtorLayout scalar-slot lowering
  + del/setTag + Prod/MProd/PProd; keep #280's SymbolicTV/epoch/path-condition work and tests;
- C3 fixed (5a xfails flip to pass), C4: default emit-lnir/emit-cabi-bindings without opt-in on a Stage1D decl ⇒ hard
  error, no helper prototypes in bindings; C5: findUnsupportedLLVMCallInCode ⇒ some for any objPtr decl (params,
  locals, ret, RC ops on objPtr) even with only isExclusive/incRef/decRef; C2 shared-object regression kept and the
  LoopVectorizeOpt proposer alias bug fixed or filed as a tracked issue; accelerators.rs budget reverted to 50 ms;
- reviewed against this checklist by both round-1 voters (Astra, Fable) before merge.
