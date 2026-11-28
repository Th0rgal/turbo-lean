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
- Production routing today: `auto` is routed by PolicyGates to con-leche when `conLecheSupported` is
  true (`routeKernelEngine`, `lean/TurboLean/PolicyGates.lean:113-118`), but the current Rust resolver
  does not probe support for `auto` — `probe_con_leche_support_for_selection` probes only for explicit
  `con-leche`/`both` selections and returns an unconditional `None` stub otherwise
  (`crates/turbo-lean/src/kernel.rs:207-221`) — so production `auto` currently resolves to the
  standard Lean kernel.
- **Not yet inventoried**: end-to-end confirmation of the engine that executes for each CLI entrypoint
  on a built binary (needs a build; none were run for this docs pass).

## 2. The `LCNF` semantics

- `lean/LeanNative/IR/RealLCNFSemantics.lean` — an operational semantics of real
  `Lean.Compiler.LCNF` declarations (namespace at `RealLCNFSemantics.lean:7`, section header at `:14`,
  ends at `:872`).
- Independence caveat, stated honestly: `lean/LeanNative/IR/RealLCNFBridge.lean:17` calls it the
  "independent `RealLCNFSemantics` evaluator", while `roadmap/HORIZONS.md` ("What the review found")
  records that it imports the lowerer's file and shares layout/type-lowering definitions. Both are
  claims-in-files; whether the semantics is independent of the lowerer is **not yet established** —
  that separation is leaf `H1.1` in the work graph (acceptance: shared definitions separated).

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

1. `RealLCNFSemantics` agrees with Lean's own evaluation — differential test not landed (`H1.1`,
   acceptance `mismatch_count == 0`; no such test result exists yet).
2. The H1 theorem statement is not frozen or hash-pinned yet (`H1.F` is an open leaf).
3. No generated coverage matrix exists yet (`H1.0` is an open leaf; no JSON is committed).
4. The `Contract V4 M2`/`M3` theorems are stated over the in-repo `"OLEN"` v1 model — `ConLeche.lean`
   says so in-file (module docstring: "binary `"OLEN"` v1 … shard model format, NOT raw Lean 4
   `.olean`"), as does the root `README.md:42`. Leaf `G1b` adds a real-`.olean` layer in the same
   file (section "Real Lean 4 v4.35.0 `.olean` Header & Root-Bounds Validator"):
   `parseRealOleanHeader` checks the 96-byte v4.35.0 header (magic `"olean"`, version `2`/`3`,
   NUL-padded `"4.35.0"`, githash `eb6cafb7…`, little-endian `base_addr` and root pointer) and that
   the root lands 8-aligned inside the object region; `parseRealOleanHeader_iff`,
   `olen_shard_not_real_olean`, `real_olean_bridge_sound` and `real_olean_checkDecl_sound` are
   kernel-checked with `0 sorryAx` and only `propext`, `Quot.sound`, `Classical.choice`.
   **Trusted, not proved:** the compacted object region is decoded into declarations by Lean's C
   runtime (`lean_compacted_region_read`, called from `readModuleData`). The Lean model takes that
   reader's output as the `decoded` argument of `parseRealOlean`; the theorems say those
   declarations are CIC-valid in the `ConLeche` model once the header passes, not that the reader
   decodes the region faithfully, nor that the `ConLeche` model is Lean's kernel. The header layout
   was checked against all 2,546 `.olean` files of the v4.35.0 toolchain, not proved from Lean's C
   sources. The kernel-backed witness of leaf `A2`
   (`audit-spec --kernel`) reads real `.olean` files through Lean's own kernel replay, but it
   trusts Lake's trace and `.hash` sidecars to bind the `.olean` to its source: an attacker who
   rewrites the `.olean`, its sidecar and its trace consistently is caught only by the kernel
   replay itself, not by the freshness check.
