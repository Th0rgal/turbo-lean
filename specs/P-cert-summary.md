# P-cert v3 (gpt-6.1-sol, executed; VM lost after completion — evidence = mission 6810286a transcript, seq 87-92)
T277 = feat/opt-in-allow-rc-adt @3277685, T280 = feat/stage1d-heap-adt-perceus-rc @e26c3ed, Lean 4.35.0
- C1 (T277 BoxU64 scalar-field miscompile): NOT_REPRODUCED. original + @[noinline] match Lean on 0/7/2^63;
  polymorphic variants fail at emit (exit 1) = rejected, not miscompiled.
- C2 (T277 LoopVectorizeOpt alias): raw pass proposal changes a shared-object test false->true (wrong), but
  SymbolicTV.validateTranslationDecl rejects (passed=false, concreteRefines=false, 0/64 samples) and the pass keeps
  the original body (changed=false). Not a miscompile; latent bug in the proposer.
- C3 (decRef fuel truncation): REPRODUCED on T277 (100 owning edges to one child -> child rc left at 65, decRef
  returns ok). T280: tested deep/wide graphs freed fully; explicitly underfueled helper returns ok with live children.
- C4 (T280 default emit-lnir emits Stage1D heap helpers w/o opt-in): REPRODUCED; compile-llvm rejects cleanly
  (no output), emit-cabi-bindings succeeds (helper prototypes leak); scalar results match Lean.
- C5 (T280 LLVM untagged load): REPRODUCED; findUnsupportedLLVMCallInCode returns none for objPtr decl using only
  isExclusive/incRef/decRef; emitter prints direct `load i32` from the object pointer, no tag check.
VERDICT (mission definition): CLEAN — no miscompilation reproduced; C3/C4/C5 are real defects.
