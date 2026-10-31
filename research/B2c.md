# B2c: elaborated-interface cutoff and optimistic kernel reuse

Across 19 incremental transitions, module cutoff could avoid **79.23%** of dependent-module rebuild seconds (8,790.044 / 11,094.962 s). Declaration reuse could optimistically avoid **97.93%** of measured kernel CPU in actually rebuilt modules.

**DIAGNOSTIC ONLY. Declaration reuse is an OPTIMISTIC UPPER BOUND, not a sound cache design.** The key omits `LEAN_NAT_MAX_SIZE`, module-mode `Lean.reduceBool` axiom information, unit-like eta dependencies through constructor field counts, and implicit Bool/Nat dependencies. No optimization is implemented.

## Scope and denominators

The 20 first-parent commits end at `5018b95`; C1 is `62fa93f0`. This uses only the import cone of `FV.Backend.Proof.{DefGenTab,IselSzTab,IselCtlTry}` and `FV.Opt.Proof.RuleArith`, not all FV. C1 is a cold baseline and is excluded from transition shares. Primary savings count only modules Lake actually rebuilt in C2–C20. Full-cone replays also check unchanged modules, but those are not credited as incremental savings.

| Measure | Seconds | Share |
|---|---:|---:|
| Dependent-module cutoff / dependent rebuild elapsed | 8,790.044 | 79.23% |
| Module cutoff / total module build elapsed | 8,790.044 | 58.66% |
| Module cutoff elapsed work / total build wall | 8,790.044 | 58.60% |
| Module cutoff / total build CPU | 13,482.532 | 62.20% |
| Kernel in cutoff-skippable modules / rebuilt kernel CPU | 5,104.260 | 63.64% |
| Optimistic declaration reuse / rebuilt kernel CPU | 7,855.267 | 97.93% |
| Optimistic declaration CPU work / total build wall | 7,855.267 | 52.37% |
| Optimistic declaration reuse / total build CPU | 7,855.267 | 36.24% |

Denominators: 8,021.087 s rebuilt-module kernel CPU; 21,674.404 s total build process-tree CPU (including 21,453.469 s in measured Lean module processes); 14,984.255 s summed module build elapsed; 14,999.378 s total build wall. Summed concurrent module elapsed is work, not critical-path wall speedup. CPU shares use CPU in both numerator and denominator. CPU-work/build-wall ratios are normalization figures, not predicted wall speedups. The two avoidance mechanisms overlap and must not be added.

## Method and checks

Lean v4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) extracts explicit tagged expression DAGs, structured names, ordered level parameters, and complete ConstantInfo metadata. The Expr-v3-retained-nodes serializer retains expressions and memoizes by address; addresses and cached Expr.hash values never enter digests. Child digests replace DAG indices, so sharing and allocation do not affect keys. Binder names, annotations, metadata, and syntax source positions are preserved. The companion hashes canonical UTF-8 JSON with SHA-256 and collapses interface dependency SCCs. Theorem IF omits the proof; all other kinds include values, safety, hints, and inductive metadata. K includes the proof and dependency IFs. Module IF is the sorted multiset of constant IFs. Repeated stored names retain their individual IF inputs, while constant references resolve to the actual imported binding returned by Lean. Noncanonical occurrences have no incoming name references and use their own payload with canonical dependency IFs. This is recorded as IF-v2-canonical-lookups. FV uses legacy modules, whose stored constants are available to importers, including private kernel names.

A custom driver calls `Lean.Kernel.Environment.addDecl` in module import order, with dependency order within modules. Unsafe/partial recursive definitions use mutual kernel groups, including singleton recursion. Inductives are replayed as groups; generated constructors/recursors are compared with the stored metadata. Duplicate theorem bodies are rechecked under a fresh name rather than skipped. Every stored constant must map to a replayed group. Native `CLOCK_PROCESS_CPUTIME_ID` readings surround each kernel call; imports, reconstruction, traversal, output, and timers remain in separately reported overhead. Total CPU includes process startup and driver elaboration; startup CPU and replay-main CPU are also recorded separately. All commits satisfy summed kernel CPU ≤ total replay CPU.

The required interface/key fixtures and four structural distinction fixtures pass, along with SCC propagation, row-order independence, missing-dependency rejection, and DAG sharing/index invariance. Two fresh Lean processes produce identical fixture serialization and hashes. `Init.Prelude` replay covers 2,324 constants with 2,033 kernel calls; full `Init` validation covers 64,849 calls.

`LEAN_NUM_THREADS=4`, `FV_MEMCAP=16G`. Lake v4.34.1 rejects `-j4`; an isolated shim accepts it and enforces at most four active Lean module builds with file locks. The first cold build exceeded 16 GiB and was killed; its failed-attempt data is retained, and subsequent builds serialize module processes. The shim also passes `-j4` directly to Lean. C1 is excluded from all transition ratios. All builds run through `scripts/memcap.sh`; C3 extraction/hash logs record its process-tree RSS watchdog fallback because user-systemd was unreachable. This fallback uses an RSS polling watchdog; sampling can miss short-lived children. Module timers exclude semaphore waiting and include Lean elaboration/code generation. Artifact-cache restore is disabled. Shared toolchain files are unchanged.

An interrupted C17 replay is preserved separately under `b2c_data/e9a91e8a/interrupted_replay_1/` and excluded from all successful replay totals and avoidance figures. C17 uses a complete fresh replay; its original successful measured build remained unchanged. The resume artifact-check build under `b2c_data/recovery/` is also explicitly excluded. Partial replay calls and CPU were never combined with the successful attempt.

Counterfactual cutoff propagates a rebuild only through imports whose elaborated IF changed, while preserving local source invalidations. Modules whose observed IF changed are never credited as avoidable; unexplained IF changes are recorded as additional invalidations. Any lakefile/manifest/toolchain change conservatively invalidates every module. Unchanged-source rebuilt modules form the dependent-rebuild denominator. The module IF describes its own stored constants and the cutoff compares direct imports. Attribute/tactic/environment effects outside that interface and visibility through transitive imports need additional modeling; this is not a proof that such a cutoff is safe for elaboration.

## Kernel reuse by kind (optimistic)

| Kind | Reusable kernel seconds | Share of kernel | Share of build CPU |
|---|---:|---:|---:|
| definition | 18.023 | 0.22% | 0.08% |
| opaque | <0.001 | <0.01% | <0.01% |
| theorem | 7,837.243 | 97.71% | 36.16% |

definition: `Backend.Insn.armFields` (d727bbc4, 2.059 ms); `Backend.armBits` (d727bbc4, 1.672 ms); `Backend.lowerFunction` (b950dc29, 1.323 ms).

opaque: `iselDestructGoal` (d727bbc4, 0.014 ms); `Backend.Proof.FlowSplit.collectSparse` (b950dc29, 0.009 ms).

theorem: `Backend.Proof.ispec_mapRegs` (d727bbc4, 23673.075 ms); `Backend.Proof.Driver.stmtLoop` (5018b950, 14801.261 ms); `Backend.Proof.Driver.termPart_ok` (5018b950, 14458.267 ms).

## Kernel inside cutoff-skippable modules, by kind

Module build seconds cannot be apportioned to declaration kinds without inventing an allocation. The kind split below uses measured kernel CPU within modules the cutoff would skip.

| Kind | Kernel seconds | Share of rebuilt kernel | Share of build CPU |
|---|---:|---:|---:|
| definition | 9.310 | 0.12% | 0.04% |
| inductive | 0.130 | <0.01% | <0.01% |
| opaque | <0.001 | <0.01% | <0.01% |
| theorem | 5,094.821 | 63.52% | 23.51% |

definition: `Backend.Insn.armFields` (b950dc29, 1.987 ms); `Backend.armBits` (b950dc29, 1.593 ms); `Backend.lowerFunction` (b950dc29, 1.323 ms).

inductive: `Isle.Interp.USoundAt` (b950dc29, 5.063 ms); `Backend.Insn` (b950dc29, 4.013 ms); `Backend.Proof.Driver.LowerShape` (d727bbc4, 3.526 ms).

opaque: `iselDestructGoal` (d727bbc4, 0.014 ms).

theorem: `Backend.Proof.ispec_mapRegs` (b950dc29, 22922.650 ms); `Backend.Proof.runTerm_lower_rule` (d727bbc4, 14080.673 ms); `Backend.Proof.Driver.stmtLoop` (d727bbc4, 13982.721 ms).

## Top 20 modules: optimistic kernel reuse

Shares use the aggregate rebuilt-kernel and total build CPU denominators above.

| Module | Reusable kernel seconds | Share of rebuilt kernel | Share of build CPU |
|---|---:|---:|---:|
| `FV.Backend.Proof.DefGenTab` | 2,243.570 | 27.97% | 10.35% |
| `FV.Backend.Proof.IselSzTab` | 1,826.887 | 22.78% | 8.43% |
| `FV.Backend.Proof.KillTab` | 1,095.104 | 13.65% | 5.05% |
| `FV.Backend.Proof.IselCovTab` | 989.414 | 12.34% | 4.56% |
| `FV.Backend.Proof.LogicImmComplete` | 307.103 | 3.83% | 1.42% |
| `FV.Backend.Proof.IselContract` | 187.676 | 2.34% | 0.87% |
| `FV.Backend.Proof.LowerLoopRun` | 126.425 | 1.58% | 0.58% |
| `FV.Backend.Proof.IselFlowRootT` | 108.551 | 1.35% | 0.50% |
| `FV.Backend.Proof.IselFlowRootF` | 102.424 | 1.28% | 0.47% |
| `FV.Backend.Proof.IselData` | 85.198 | 1.06% | 0.39% |
| `FV.Backend.Proof.IselFlowTabT` | 82.214 | 1.02% | 0.38% |
| `FV.Backend.Proof.IselContractP` | 81.597 | 1.02% | 0.38% |
| `FV.Backend.Proof.IselFlowTabF` | 77.351 | 0.96% | 0.36% |
| `FV.Backend.Proof.IselTermFactsRules` | 72.551 | 0.90% | 0.33% |
| `FV.Backend.Proof.IselCtl` | 70.221 | 0.88% | 0.32% |
| `FV.Backend.Proof.CSemRename` | 55.935 | 0.70% | 0.26% |
| `FV.Backend.Proof.IselTermFactsBase` | 55.026 | 0.69% | 0.25% |
| `FV.Backend.Proof.IselExcl` | 29.329 | 0.37% | 0.14% |
| `FV.Backend.Proof.IselCtlUnmatch` | 24.640 | 0.31% | 0.11% |
| `FV.Backend.Proof.SpillEdgesIsel` | 23.498 | 0.29% | 0.11% |

`FV.Backend.Proof.DefGenTab`: `Backend.Proof.DefGen.defTab_termOk` (d727bbc4, 35.867 ms); `Backend.Proof.DefGen.rootLower_ok` (d727bbc4, 18.782 ms); `Backend.Proof.DefGen.tabOK` (d727bbc4, 0.838 ms).

`FV.Backend.Proof.IselSzTab`: `Backend.Proof.Cov.szStmt_ok` (d727bbc4, 20.055 ms); `Backend.Proof.Cov.tgTerm_ok` (d727bbc4, 18.044 ms); `Backend.Proof.Cov.szTerm_ok` (d727bbc4, 17.788 ms).

`FV.Backend.Proof.KillTab`: `Backend.Proof.Kill.tabOkB_S` (d727bbc4, 264.945 ms); `Backend.Proof.Kill.noX_ok` (d727bbc4, 129.597 ms); `Backend.Proof.Kill.nop_rhs_some` (d727bbc4, 80.554 ms).

`FV.Backend.Proof.IselCovTab`: `Backend.Proof.Cov.covStmt_ok` (d727bbc4, 21.164 ms); `Backend.Proof.Cov.covTerm_ok` (d727bbc4, 18.434 ms); `Backend.Proof.Cov.covStmtTop_ok` (d727bbc4, 17.324 ms).

`FV.Backend.Proof.LogicImmComplete`: `Backend.Proof.Cov.logicImmComplete` (d727bbc4, 4.121 ms); `Backend.Proof.Cov.LogicImm.run_of_two` (d727bbc4, 2.900 ms); `Backend.Proof.Cov.LogicImm.pat_of_accept` (d727bbc4, 1.626 ms).

`FV.Backend.Proof.IselContract`: `Backend.Proof.branchOk_runTerm` (d727bbc4, 13863.029 ms); `Backend.Proof.tryIndOk_runTerm` (d727bbc4, 13818.537 ms); `Backend.Proof.lowerInstOk_runTerm` (d727bbc4, 13752.139 ms).

`FV.Backend.Proof.LowerLoopRun`: `Backend.Proof.Driver.stmtLoop` (5018b950, 14801.261 ms); `Backend.Proof.Driver.termPart_ok` (5018b950, 14458.267 ms); `Backend.Proof.Driver.termTry` (5018b950, 13983.829 ms).

`FV.Backend.Proof.IselFlowRootT`: `Backend.Proof.Flow.tlsRules_eq` (d727bbc4, 98.655 ms); `Backend.Proof.Flow.tlsRoot_ok` (d727bbc4, 0.612 ms); `Backend.Proof.Flow.tlsRootBranch_ok` (d727bbc4, 0.190 ms).

`FV.Backend.Proof.IselFlowRootF`: `Backend.Proof.Flow.flowRules_eq` (d727bbc4, 90.962 ms); `Backend.Proof.Flow.flowRoot_ok` (d727bbc4, 0.641 ms); `Backend.Proof.Flow.flowRules18` (d727bbc4, 0.089 ms).

`FV.Backend.Proof.IselData`: `Backend.Proof.program_term_1979` (b950dc29, 292.795 ms); `Backend.Proof.program_term_2269` (b950dc29, 108.554 ms); `Backend.Proof.program_term_2470` (b950dc29, 108.525 ms).

`FV.Backend.Proof.IselFlowTabT`: `Backend.Proof.Flow.tlsTab_ok` (d727bbc4, 0.642 ms); `Backend.Proof.Flow.tlsTab9_ok` (d727bbc4, 0.122 ms); `Backend.Proof.Flow.tlsTab15_ok` (d727bbc4, 0.120 ms).

`FV.Backend.Proof.IselContractP`: `Backend.Proof.tryIndOkP_runTerm` (d727bbc4, 13811.697 ms); `Backend.Proof.lowerInstOkP_runTerm` (d727bbc4, 13576.836 ms); `Backend.Proof.tryOkP_runTerm` (d727bbc4, 13536.574 ms).

`FV.Backend.Proof.IselFlowTabF`: `Backend.Proof.Flow.flowTab_ok` (d727bbc4, 0.726 ms); `Backend.Proof.Flow.flowTab8_ok` (d727bbc4, 0.119 ms); `Backend.Proof.Flow.flowTab5_ok` (d727bbc4, 0.119 ms).

`FV.Backend.Proof.IselTermFactsRules`: `Backend.Proof.tbz_shape` (5018b950, 191.500 ms); `Backend.Proof.tbnz_shape` (5018b950, 106.341 ms); `Backend.Proof.brTable_shape` (5018b950, 61.352 ms).

`FV.Backend.Proof.IselCtl`: `Backend.Proof.mem_lower_2574` (d727bbc4, 7.353 ms); `Backend.Proof.mem_lower_2237` (d727bbc4, 7.138 ms); `Backend.Proof.mem_lower_2518` (d727bbc4, 7.136 ms).

`FV.Backend.Proof.CSemRename`: `Backend.Proof.ispec_mapRegs` (d727bbc4, 23673.075 ms); `Backend.Proof.formOk_mapRegs` (d727bbc4, 1363.306 ms); `Backend.Proof.mspec_mapRegs` (d727bbc4, 560.630 ms).

`FV.Backend.Proof.IselTermFactsBase`: `Backend.Proof.runTerm_lower_rule` (d727bbc4, 14080.673 ms); `Backend.Proof.runTerm_lower_branch_rule` (d727bbc4, 13790.011 ms); `Backend.Proof.refines_ispec` (d727bbc4, 0.113 ms).

`FV.Backend.Proof.IselExcl`: `Backend.Proof.excludedUnmatchable` (d727bbc4, 1.583 ms); `Backend.Proof.exclOk_program` (d727bbc4, 1.565 ms).

`FV.Backend.Proof.IselCtlUnmatch`: `Backend.Proof.fmtKinds_program` (d727bbc4, 39.911 ms); `Backend.Proof.branchExcludedUnmatchable` (d727bbc4, 2.141 ms); `Backend.Proof.rootFmt_match_k` (d727bbc4, 1.820 ms).

`FV.Backend.Proof.SpillEdgesIsel`: `Backend.Proof.trap_shapeT` (d727bbc4, 37.308 ms); `Backend.Proof.ret_shapeT` (d727bbc4, 35.052 ms); `Backend.Proof.jump_shapeJ` (d727bbc4, 29.554 ms).

## Top 20 modules: module cutoff

Elapsed shares use all dependent-module rebuild seconds; CPU shares use total build process-tree CPU. The kernel columns count measured kernel work inside the skippable modules.

| Module | Avoidable build elapsed | Share of dependent elapsed | Share of build CPU | Kernel seconds | Share of rebuilt kernel |
|---|---:|---:|---:|---:|---:|
| `FV.Backend.Proof.IselSzTab` | 1,874.595 | 16.90% | 8.65% | 1,826.887 | 22.78% |
| `FV.Backend.Proof.RegallocAtomic` | 1,058.887 | 9.54% | 4.93% | 0.261 | <0.01% |
| `FV.Backend.Proof.IselCovTab` | 1,019.703 | 9.19% | 4.70% | 989.414 | 12.34% |
| `FV.Backend.Proof.DefGenTab` | 851.384 | 7.67% | 3.91% | 753.147 | 9.39% |
| `FV.Backend.Proof.KillTab` | 579.862 | 5.23% | 2.67% | 557.676 | 6.95% |
| `FV.Backend.Proof.LogicImmComplete` | 322.997 | 2.91% | 1.50% | 307.103 | 3.83% |
| `FV.Backend.Proof.IselCmpEmit` | 215.512 | 1.94% | 1.03% | 1.915 | 0.02% |
| `FV.Backend.Proof.CSemRename` | 212.020 | 1.91% | 1.12% | 27.524 | 0.34% |
| `FV.Backend.Proof.IselCmpIcmp` | 177.052 | 1.60% | 0.88% | 2.549 | 0.03% |
| `FV.Backend.Proof.RegallocCover` | 130.120 | 1.17% | 0.94% | 2.172 | 0.03% |
| `FV.Backend.Proof.IselTermFactsRules` | 111.898 | 1.01% | 0.65% | 24.465 | 0.31% |
| `FV.Opt.Proof.RuleArithP5` | 108.137 | 0.97% | 3.20% | 6.224 | 0.08% |
| `FV.Opt.Proof.RuleArithP1` | 106.838 | 0.96% | 4.00% | 6.119 | 0.08% |
| `FV.Opt.Proof.RuleArithP4` | 105.273 | 0.95% | 3.05% | 5.976 | 0.07% |
| `FV.Opt.Proof.RuleArithP2` | 103.673 | 0.93% | 3.42% | 5.978 | 0.07% |
| `FV.Opt.Proof.RuleArithP3` | 100.236 | 0.90% | 3.65% | 5.789 | 0.07% |
| `FV.Backend.Proof.IselContractP` | 93.277 | 0.84% | 0.43% | 81.602 | 1.02% |
| `FV.Backend.Proof.IselCtlTbz` | 88.579 | 0.80% | 0.48% | 0.540 | <0.01% |
| `FV.Backend.Proof.IselCtl` | 81.930 | 0.74% | 0.38% | 70.221 | 0.88% |
| `FV.Backend.Proof.IselFlowRootT` | 54.002 | 0.49% | 0.25% | 54.913 | 0.68% |

`FV.Backend.Proof.IselSzTab`: `Backend.Proof.Cov.szStmt_ok` (d727bbc4, 20.055 ms); `Backend.Proof.Cov.tgTerm_ok` (d727bbc4, 18.044 ms); `Backend.Proof.Cov.szTerm_ok` (d727bbc4, 17.788 ms).

`FV.Backend.Proof.RegallocAtomic`: `Backend.Proof.corr_csetm` (b950dc29, 139.741 ms); `Backend.Proof.corr_loadAcquire` (b950dc29, 40.021 ms); `Backend.Proof.corr_storeRelease` (b950dc29, 33.590 ms).

`FV.Backend.Proof.IselCovTab`: `Backend.Proof.Cov.covStmt_ok` (d727bbc4, 21.164 ms); `Backend.Proof.Cov.covTerm_ok` (d727bbc4, 18.434 ms); `Backend.Proof.Cov.covStmtTop_ok` (d727bbc4, 17.324 ms).

`FV.Backend.Proof.DefGenTab`: `Backend.Proof.DefGen.defTab_termOk` (d727bbc4, 35.867 ms); `Backend.Proof.DefGen.rootLower_ok` (d727bbc4, 18.782 ms); `Backend.Proof.DefGen.tabOK` (d727bbc4, 0.838 ms).

`FV.Backend.Proof.KillTab`: `Backend.Proof.Kill.tabOkB_S` (d727bbc4, 264.945 ms); `Backend.Proof.Kill.noX_ok` (d727bbc4, 129.597 ms); `Backend.Proof.Kill.nop_rhs_some` (d727bbc4, 80.554 ms).

`FV.Backend.Proof.LogicImmComplete`: `Backend.Proof.Cov.logicImmComplete` (d727bbc4, 4.121 ms); `Backend.Proof.Cov.LogicImm.run_of_two` (d727bbc4, 2.900 ms); `Backend.Proof.Cov.LogicImm.pat_of_accept` (d727bbc4, 1.626 ms).

`FV.Backend.Proof.IselCmpEmit`: `Backend.Proof.emit_icmp_okT` (d727bbc4, 531.136 ms); `Backend.Proof.mkVariant_intcc` (d727bbc4, 42.813 ms); `Backend.Proof.lower_extend_op_ok` (d727bbc4, 20.250 ms).

`FV.Backend.Proof.CSemRename`: `Backend.Proof.ispec_mapRegs` (b950dc29, 22922.650 ms); `Backend.Proof.formOk_mapRegs` (b950dc29, 1318.091 ms); `Backend.Proof.mspec_mapRegs` (b950dc29, 540.633 ms).

`FV.Backend.Proof.IselCmpIcmp`: `Backend.Proof.is_nonzero_okT` (d727bbc4, 993.429 ms); `Backend.Proof.cri_ok` (d727bbc4, 67.233 ms); `Backend.Proof.setsFlags_tst255` (d727bbc4, 38.730 ms).

`FV.Backend.Proof.RegallocCover`: `Backend.Proof.formOk_sound` (b950dc29, 499.785 ms); `Backend.Proof.formOk_fpuLoad` (b950dc29, 86.442 ms); `Backend.Proof.formOk_store` (b950dc29, 85.775 ms).

`FV.Backend.Proof.IselTermFactsRules`: `Backend.Proof.tbz_shape` (d727bbc4, 190.093 ms); `Backend.Proof.tbnz_shape` (d727bbc4, 105.500 ms); `Backend.Proof.brTable_shape` (d727bbc4, 61.335 ms).

`FV.Opt.Proof.RuleArithP5`: `Opt.Proof.ok_rule_arithmetic_308` (b950dc29, 197.694 ms); `Opt.Proof.ok_rule_arithmetic_324` (b950dc29, 195.760 ms); `Opt.Proof.ok_rule_arithmetic_233` (b950dc29, 157.850 ms).

`FV.Opt.Proof.RuleArithP1`: `Opt.Proof.ok_rule_arithmetic_424` (b950dc29, 184.443 ms); `Opt.Proof.ok_rule_arithmetic_556` (b950dc29, 161.936 ms); `Opt.Proof.ok_rule_arithmetic_498` (b950dc29, 150.408 ms).

`FV.Opt.Proof.RuleArithP4`: `Opt.Proof.ok_rule_arithmetic_307` (b950dc29, 197.591 ms); `Opt.Proof.ok_rule_arithmetic_323` (b950dc29, 195.831 ms); `Opt.Proof.ok_rule_arithmetic_572` (b950dc29, 164.273 ms).

`FV.Opt.Proof.RuleArithP2`: `Opt.Proof.ok_rule_arithmetic_506` (b950dc29, 162.720 ms); `Opt.Proof.ok_rule_arithmetic_312` (b950dc29, 153.576 ms); `Opt.Proof.ok_rule_arithmetic_512` (b950dc29, 152.578 ms).

`FV.Opt.Proof.RuleArithP3`: `Opt.Proof.ok_rule_arithmetic_526` (b950dc29, 161.644 ms); `Opt.Proof.ok_rule_arithmetic_520` (b950dc29, 161.041 ms); `Opt.Proof.ok_rule_arithmetic_532` (b950dc29, 151.676 ms).

`FV.Backend.Proof.IselContractP`: `Backend.Proof.tryIndOkP_runTerm` (d727bbc4, 13811.697 ms); `Backend.Proof.lowerInstOkP_runTerm` (d727bbc4, 13576.836 ms); `Backend.Proof.tryOkP_runTerm` (d727bbc4, 13536.574 ms).

`FV.Backend.Proof.IselCtlTbz`: `Backend.Proof.tbz_ruleOk` (d727bbc4, 205.782 ms); `Backend.Proof.tbnz_ruleOk` (d727bbc4, 118.584 ms); `Backend.Proof.tbb_ok` (d727bbc4, 37.328 ms).

`FV.Backend.Proof.IselCtl`: `Backend.Proof.mem_lower_2574` (d727bbc4, 7.353 ms); `Backend.Proof.mem_lower_2237` (d727bbc4, 7.138 ms); `Backend.Proof.mem_lower_2518` (d727bbc4, 7.136 ms).

`FV.Backend.Proof.IselFlowRootT`: `Backend.Proof.Flow.tlsRules_eq` (d727bbc4, 98.655 ms); `Backend.Proof.Flow.tlsRoot_ok` (d727bbc4, 0.612 ms); `Backend.Proof.Flow.tlsRootBranch_ok` (d727bbc4, 0.190 ms).

## Commit transitions

| Commit | Built modules | Cutoff seconds | Optimistic reusable kernel seconds |
|---|---:|---:|---:|
| `22f3190e` | 0 | 0.000 | 0.000 |
| `d727bbc4` | 203 | 4,483.845 | 3,494.411 |
| `08d4bf83` | 0 | 0.000 | 0.000 |
| `e87a5aa6` | 0 | 0.000 | 0.000 |
| `75ec10ef` | 0 | 0.000 | 0.000 |
| `1acfcfc3` | 0 | 0.000 | 0.000 |
| `719f226f` | 0 | 0.000 | 0.000 |
| `f889e936` | 0 | 0.000 | 0.000 |
| `76964a87` | 0 | 0.000 | 0.000 |
| `81cdac89` | 0 | 0.000 | 0.000 |
| `c533c22a` | 0 | 0.000 | 0.000 |
| `0ec56b32` | 0 | 0.000 | 0.000 |
| `6f9f8334` | 0 | 0.000 | 0.000 |
| `549e0c2f` | 0 | 0.000 | 0.000 |
| `e14718a2` | 0 | 0.000 | 0.000 |
| `e9a91e8a` | 0 | 0.000 | 0.000 |
| `73bbb15d` | 0 | 0.000 | 0.000 |
| `b950dc29` | 278 | 4,278.722 | 3,516.383 |
| `5018b950` | 29 | 27.477 | 844.472 |

## Replay accounting

These are complete-cone replay CPU measurements, including modules Lake did not rebuild. Overhead is total process CPU minus summed addDecl CPU; startup is included in that overhead. Each dataset independently checks the CPU bound.

| Commit | Summed kernel CPU seconds | Replay overhead seconds | Total process CPU seconds |
|---|---:|---:|---:|
| `62fa93f0` | 3,559.484 | 19.661 | 3,579.145 |
| `22f3190e` | 3,569.464 | 19.721 | 3,589.185 |
| `d727bbc4` | 3,745.600 | 21.232 | 3,766.832 |
| `08d4bf83` | 3,736.007 | 21.275 | 3,757.281 |
| `e87a5aa6` | 3,740.818 | 20.704 | 3,761.522 |
| `75ec10ef` | 3,739.262 | 20.957 | 3,760.219 |
| `1acfcfc3` | 3,798.856 | 20.741 | 3,819.596 |
| `719f226f` | 3,846.198 | 22.443 | 3,868.642 |
| `f889e936` | 3,734.014 | 22.848 | 3,756.861 |
| `76964a87` | 3,747.512 | 20.680 | 3,768.193 |
| `81cdac89` | 3,747.980 | 20.525 | 3,768.506 |
| `c533c22a` | 3,757.945 | 20.480 | 3,778.426 |
| `0ec56b32` | 3,740.957 | 20.802 | 3,761.759 |
| `6f9f8334` | 3,721.356 | 20.737 | 3,742.093 |
| `549e0c2f` | 3,776.224 | 20.920 | 3,797.144 |
| `e14718a2` | 3,758.668 | 20.837 | 3,779.506 |
| `e9a91e8a` | 3,665.348 | 21.967 | 3,687.315 |
| `73bbb15d` | 3,634.432 | 20.136 | 3,654.568 |
| `b950dc29` | 3,595.375 | 19.438 | 3,614.813 |
| `5018b950` | 3,106.828 | 25.923 | 3,132.751 |

## Artifacts and limits

`B2c.json` contains denominators, all module buckets, transitions, replay totals, and key-bearing examples. `b2c_data/<commit>/rows.jsonl.gz` stores name/kind/module/IF/K/kernel_ms, with group times charged once to the representative. `kernel_groups.jsonl.gz` retains every measured call; repeated K values retain their occurrence times. `replay.jsonl.gz`, source hashes, build logs, per-module CPU/elapsed timings, and coverage checks preserve the evidence. Each completed commit was pushed to `research/b2c-measurement` before advancing; no PR was opened.

Shared-host timing noise, interpreter/reconstruction overhead, and changed parallel scheduling limit wall-speedup inference. The report estimates avoidable work, not an implemented end-to-end speedup. Kernel times are replay measurements, not profiler samples of the original elaboration.

## Unmet example requirement

All 20 measurement datasets are complete. The requirement of at least three distinct non-auxiliary examples per nonzero bucket remains unmet for the buckets below. These counts include every eligible name; repeated declaration–commit occurrences cannot supply additional distinct names. The default completion audit remains strict and cannot certify this report.

| Bucket | Available distinct names | Required | Eligible names |
|---|---:|---:|---|
| reuse kind opaque | 2 | 3 | `Backend.Proof.FlowSplit.collectSparse`; `iselDestructGoal` |
| cutoff kind opaque | 1 | 3 | `iselDestructGoal` |
| reuse module FV.Backend.Proof.IselExcl | 2 | 3 | `Backend.Proof.exclOk_program`; `Backend.Proof.excludedUnmatchable` |

`B2c_example_inventory.json` exhaustively inventories the measured groups in these buckets, including excluded generated names. `B2c_source_review.json` verifies all selected examples against historical source bytes. No example requirement has been waived.
