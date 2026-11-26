# Trusted base (`docs/TRUSTED_BASE.md`)

> **Purpose**: the statement of what the proofs in this repository rest on, as required by
> [`roadmap/HORIZONS.md`](../roadmap/HORIZONS.md) ("A written trusted base (`docs/TRUSTED_BASE.md`):
> Lean's kernel, the `LCNF` semantics, the `LNIR` semantics, the LLVM printer, LLVM, the Lean runtime.").
>
> **Provenance**: written by R0b from `main` at `2ede4dd` (2026-11-16). Every entry cites a file and
> line, or a command whose output shows the claim. An entry that could not be supported from the
> repository is marked **not yet inventoried**, with the reason. Nothing here changes any statement
> in [`roadmap/VALIDATION_CONTRACTS.md`](../roadmap/VALIDATION_CONTRACTS.md).

## 1. Lean's kernel — trusted, upstream

- The toolchain is pinned by `lean/lean-toolchain` (`cat lean/lean-toolchain` → `leanprover/lean4:v4.35.0`).
  The kernel that finally accepts proofs is the upstream Lean 4 v4.35.0 kernel shipped by that toolchain.
- `turbo-lean` wraps kernel *selection*, not the kernel itself: `crates/turbo-lean/src/kernel.rs`
  (`parse_selection`, `resolve_kernel_engine_in_workspace` at `kernel.rs:281`), with the routing rule
  defined and proved in Lean: `routeKernelEngine`, `lean/TurboLean/PolicyGates.lean:113-118`.
- Production routing: `auto` is routed by PolicyGates to con-leche when `conLecheSupported` is
  true (`routeKernelEngine`, `lean/TurboLean/PolicyGates.lean:113-118`), and since G1c the Rust
  resolver probes support for `auto` too. Since G1c r2 the selection probe
  (`probe_con_leche_support_for_selection`) and every executing site (`ci-verify`, `pr-verify`
  head statements, `check --emit-olean`) share ONE discovery,
  `discover_con_leche_binary_for_selection_with_provenance` (`crates/turbo-lean/src/kernel.rs`),
  which pins the accepted binary's bytes at selection time (`ResolvedConLecheBinary`, a blake3
  digest). Before each spawn the runner opens the pinned path without following a symlink final
  component and, on Linux, copies the bytes into a sealed in-memory file while hashing them,
  then executes that sealed copy, so the executed bytes are the hashed bytes by construction —
  an in-place rewrite of the source inode after verification cannot reach the run (executing
  the source's own fd would only pin the inode, not its bytes). On other platforms the
  canonical path is spawned right after the fd hash, leaving that platform's small
  open-to-exec window. The discovery checks the pinned toolchain and the
  provisioned (`TURBO_CON_LECHE_BIN` / bridge) binaries, and for `auto` only it additionally
  accepts the toolchain-bundled binary at `$ELAN_HOME/toolchains/<pinned>/bin/con-leche`
  (`bundled_toolchain_con_leche_binary`), canonicalized, rejected when it lies under the
  checkout, and accepted only when its `--help` advertises the `--olean` mode the executing
  sites require (`con_leche_help_advertises_olean`; a bundled binary without it makes `auto`
  fall back to standard). An accepted bundled binary's rev is NOT verified, so its recorded
  `con_leche_rev` is the probed-capability marker
  (`BUNDLED_CON_LECHE_PROVENANCE_MARKER`), never the pinned rev, which is recorded for the
  identity-gated provisioned binaries only; a bundled binary reached through the provisioning
  path records the distinct `BUNDLED_CON_LECHE_PROVISIONED_MARKER`
  (`toolchain-bundled:rev-unverified:provisioned`), so the two acceptance routes stay
  distinguishable in recorded provenance. Explicit `con-leche`/`both` selections keep failing
  closed on the provisioned binaries only. Pinned both ways by
  `test_kernel_auto_selects_bundled_con_leche_on_pinned_toolchain` and the env-free selection
  matrix over `discover_con_leche_binary_for_selection_impl` (`kernel.rs`).
- **Not yet inventoried**: end-to-end confirmation of the engine that executes for each CLI entrypoint
  on a built binary (needs a build; none were run for this docs pass).

## 2. The `LCNF` semantics

- `lean/LeanNative/IR/RealLCNFSemantics.lean` — an operational semantics of real
  `Lean.Compiler.LCNF` declarations (namespace at `RealLCNFSemantics.lean:7`, section header at `:14`,
  ends at `:872`).
- Independence, as separated by `H1.1` (`8922a03`, pin `40275bc`): `RealLCNFSemantics.lean` no
  longer imports the lowerer. It and `RealLCNFBridge.lean` both import the shared-definitions module
  `lean/LeanNative/IR/RealLCNFShared.lean` (operator tables, width/mask helpers, ground type
  lowering, the C1.2 layout spec, `RealBridgeCtx`), and `lean/LeanNative/Tests/RealLCNFSeparationPin.lean`
  fails the build if the semantics' import closure reaches `RealLCNFBridge`. The semantics is thus
  independent of the lowering functions, not of the definitions in `RealLCNFShared.lean`.

## 3. The `LNIR` semantics

- `lean/LeanNative/Semantics/Eval.lean:561`: `def evalCode (fuel : Nat) : VarEnv → HeapState → LNIRCode
  → Except UBError (Val × HeapState)` — the operational interpreter the proofs and conformance
  harnesses target.
- `LNIRCode` is defined at `lean/LeanNative/IR/AST.lean:92`.
- **Not yet inventoried**: a constructor-level inventory of `Val` and the exact language coverage of
  `evalCode` (closures, big `Nat`, strings) — `roadmap/HORIZONS.md` records the IR lacks them, but an
  exhaustive constructor listing needs a full read of `IR/AST.lean`, which this pass did not do.

## 4. The proved bridge (what the above are used for)

- `theorem lowerRealLCNFDecl_sound`, `lean/LeanNative/Proofs/RealLCNFBridgeProofs.lean:479` — the
  statement `roadmap/HORIZONS.md` cites as the one proved `LCNF → LNIR` path.
- Per-case proof modules: `lean/LeanNative/Proofs/RealLCNFBridge/{CtorIntrinsic,CtorScalarCall,JpTag,LetValue,Scalar}.lean`.
- Static axiom scan (this pass, no build): `grep -c "^axiom"` returns **0** in
  `Proofs/RealLCNFBridgeProofs.lean`, `IR/RealLCNFBridge.lean`, `IR/RealLCNFSemantics.lean`, and
  `lean/TurboLean/ConLeche.lean`; `grep sorry` returns nothing in `RealLCNFBridgeProofs.lean`.
- **Not yet inventoried**: the transitive axiom closure of the proved theorems (`#print axioms
  lowerRealLCNFDecl_sound` and the audit over all theorems). The in-repo mechanism for that audit
  exists — `lean/LeanNative/Proofs/AxiomAudit.lean:831-866` (`AxiomAuditReport`; "fails the build if
  any theorem depends on `sorryAx`, `trustCompiler`, or non-standard axioms") — but running it
  requires a Lean build, which this docs pass did not do.

## 5. The LLVM printer

- Typed-AST printer with proved properties: `lean/LeanNative/Backend/LLVMAst/`, e.g.
  `theorem ppType_injective`, `lean/LeanNative/Backend/LLVMAst/RoundtripProofs.lean:212`.
- Standalone string emitter (unverified, part of the trusted base): `lean/LeanNative/Backend/LLVM.lean`
  — 2,661 LOC with 375 `s!` interpolation sites (`wc -l`; `grep -c 's!'`).
- Which printer each production target uses is **not yet inventoried** (needs driver-level tracing;
  the root `README.md:56` records `LLVM.lean` as separate from the optional `LLVMEmitVerify` path).

## 6. LLVM — trusted, external

- Used as the reference executor for differential checking: `scripts/run_llvm_lli_diff.py` runs the
  emitted module under `lli --force-interpreter` (docstring, `run_llvm_lli_diff.py:2-5`); CI runs its
  self-test at `.github/workflows/ci.yml:36`.
- **Not yet inventoried**: the pinned LLVM version — no version pin was found in the workflows or
  `crates/turbo-lean/Cargo.toml` (no `llvm-sys` dependency), so the exact LLVM the gate runs against
  is whatever the CI image provides.

## 7. The Lean runtime — trusted, upstream

- The runtime that compiled/emitted code links against is the one shipped with the toolchain pinned in
  `lean/lean-toolchain` (`leanprover/lean4:v4.35.0`).
- **Not yet inventoried**: the exact linkage of a shipped artifact (which runtime objects the produced
  binaries import) — that needs `ldd`/`nm` on a build product, and no builds were run for this pass.

## 8. Assumptions register (relied on, not proved in-repo)

1. `RealLCNFSemantics` agrees with Lean's own evaluation — tested, not proved. The `H1.1`
   differential driver (`eval-lcnf`, `lean/LeanNative/Driver/EvalLCNFCLI.lean`, landed `8922a03`)
   compares it with compiled Lean on its corpus, and the contract script fails unless
   `mismatch_count == 0` with at least 12 declarations and 100 vectors compared
   (`scripts/contract.d/35_h11_lcnf_differential.sh`). Agreement outside that corpus is assumed.
2. The H1 theorem statement is frozen and hash-pinned (`H1.F`, w-h1f 2026-11-26):
   `lean/LeanNative/SpecLocked.lean` restates `lowerRealLCNFDecl_sound` verbatim (proved by
   delegation), and an in-file `#eval` gate fails every `lake build` of the `LeanNative` library
   unless the live `ConstantInfo.type` structurally equals the frozen copy (modulo the documented
   per-declaration matcher renaming) and its `Expr.hash` equals the pinned `306234630` (measured
   on v4.35.0); the file-level SHA-256 is recorded in the freezing commit.
3. The generated coverage matrix is a measurement, not a proof (`H1.0`): `scripts/lcnf_coverage.py`
   runs the real lowerer over its corpora, the committed results (`scripts/lcnf_coverage_results.json`,
   measured at `19ae99c`) pin the bridge-source digests, and CI's `verify` job emits the JSON. A
   declaration counts as `proved` when the proved path lowers it with no local call, so
   `lowerRealLCNFDecl_sound` applies to it; the count does not re-check that theorem.
4. The `Contract V4 M2`/`M3` theorems are stated over the in-repo `"OLEN"` v1 model — `ConLeche.lean`
   says so in-file (`lean/TurboLean/ConLeche.lean:7,12`: "binary `"OLEN"` v1 … shard model format,
   NOT raw Lean 4 `.olean`"), as does the root `README.md:42`; the proof against real `.olean`
   files is open (leaf `G1b` caveat, PR `#460`), and the kernel-backed `ConstantInfo` witness is
   leaf `A2`.
