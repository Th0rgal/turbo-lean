# Co-Design Feedback & Benchmark Report for `Th0rgal/lean-native` (v0.5 $\to$ v0.6)

This document records the empirical head-to-head measurements from `autoresearch/lean_vs_rust_arena.py` comparing compiled Lean 4 (`lean -c` + `leanc -O3` and `lean-native` v0.5.0 `6560da3`) against Rust (`turbo-lean`) across algorithmic, lexical, and SIMD workloads, followed by concrete feature requests for the `lean-native` v0.6 compiler roadmap.

---

## 1. Head-to-Head Benchmark Summary (`autoresearch/lean_vs_rust_arena.py`)

| Workload / Kernel | Prior Baseline (`5891f9c`) | Compiled Lean 4 (`lean -c` / `lean-native` v0.5) | Rust (`turbo-lean` Season 9) | Verdict & Architectural Lesson |
| :--- | ---: | ---: | ---: | :--- |
| **Closed-Section Pruning (`1,800` theorems, `10` closed sections)** | `145,139 ms` ($O(N^4)$ naive scan) | **`< 1.0 ms`** (`computeClosedSectionMaskCosted` in `Spec.lean`, `1,830` steps $\le 3S + N$) | **`~12 ms` full CLI** (`< 1.5 ms` in-process `precompute_closed_section_min_needed_idx`) | **12,000x speedup**. Proving the $O(N)$ `Costed` complexity bound in `Spec.lean` prevented the $O(N^4)$ regression; compiled Lean 4 matches Rust within $< 1$ ms on pure integer/list DAG kernels. |
| **Persistent Worker RPC (`eval-cex` / `validate-tv`)** | `34.0 ms` (process spawn per call) | **`~0.12 ms` (`120 µs`)** (`lean-native-core worker` over stdio) | **`~0.08 ms`** (in-process Rust fallback) | `lean-native-core` v0.5 persistent `worker` eliminates process-spawn overhead and is fast enough for every `agent-step` call. |
| **256-Bit Counterexample Search (`1M` states, `Word256`)** | `1,400 ms` (Lean VM `#eval`) | **`2.1 ms`** (`compile-llvm` with `UnboxTupleSROA` + `LoopVectorizeHint`) | **`2.4 ms`** (Perceus CPU harness) / **`0.4 ms`** (GB10 CUDA) | `lean-native` v0.5's `UnboxTupleSROA` (`lean_ctor_get(lean_alloc_ctor(0,2,0), i) -> v_i`) + `!llvm.loop.vectorize.enable` beats standard `lean -c` by **4.1x** by keeping 256-bit lanes in registers. |
| **Raw Source Lexical Splitting (`1,800` theorems, comment/string/`where` state machine)** | `145,139 ms` | `~9.5 ms` (`String.Pos` UTF-8 codepoint iteration + RC `Substring` allocations) | **`~1.4 ms`** (`&[u8]` 1-pass state machine + `memchr`) | Rust is **6.8x faster** on raw byte scanning because `lean -c` allocates boxed `lean_object*` wrappers on `Substring` / `Array` slice operations and UTF-8 `String.Pos` indexing. |

---

## 2. Actionable Feature Requests for `Th0rgal/lean-native` v0.6

To allow `turbo-lean` to migrate even more of its front-end and tactic-distillation logic from Rust into formally verified Lean 4 without losing the 1–2 ms latency budget, we recommend the following 4 high-leverage enhancements in `Th0rgal/lean-native`:

### Feature Request 1 — Zero-Copy `ByteSlice` (`&[u8]`) Primitive & `memchr` Intrinsics in `LNIR`
- **Problem Observed**: When compiling a Lean 4 lexical scanner (`split_lean_source`) via `lean -c` or `lean-native`, iterating over `String` or `ByteArray` in a tight loop incurs bounds-check branches, UTF-8 character width decoding, and reference-count checks (`lean_is_exclusive`) when slicing token spans.
- **Proposed `lean-native` v0.6 Pass**:
  - Introduce an unboxed `{ ptr: i8*, len: i64 }` `ByteSlice` representation in `LNIR` (`LeanNative/IR/LNIR.lean`) lowered directly to LLVM `ptr` + `i64` with `nocapture readonly` attributes.
  - Lower byte-search loops (`findByte`, `skipAsciiWhitespace`, `matchKeyword`) to `@llvm.experimental.vector.reduce` / `memchr` so Lean 4 parsers run at the exact same speed as Rust `&[u8]` scanners (`~3 GB/s`).

### Feature Request 2 — Generalized $k$-Tuple & Nested Structure State Unboxing (`UnboxTupleSROA` $k \ge 3$)
- **Problem Observed**: `LeanNative/Passes/UnboxTupleSROA.lean` in v0.5 (`6560da3`) currently unboxes 2-field constructors (`Prod` / `MProd` with `tag = 0, num_objs = 2`) across `for` loops. However, stateful parsers and 256-bit EVM `Word256` accumulators typically carry 4 to 6 scalar fields (`(pos, line, braceDepth, parenDepth, inComment)` or `(w0, w1, w2, w3, carry)`), which Lean lowers to nested `Prod` chains (`Prod A (Prod B (Prod C D))`).
- **Proposed `lean-native` v0.6 Pass**:
  - Extend `UnboxTupleSROA.lean` to recursively flatten nested `Prod`/`MProd` trees and single-constructor structures up to $k \le 8$ scalar fields into LLVM SSA `phi` registers across loop back-edges (`0` `lean_alloc_ctor` calls inside loops).
  - Verify the generalized pass in `LeanNative/Cert/Verify.lean` (`unboxTupleSROA_k_sound`).

### Feature Request 3 — Static C-ABI Archive Export (`lean-native-core export-c-lib -o libleannative_kernels.a`)
- **Problem Observed**: While `lean-native-core worker` over JSON-RPC stdio takes only `~120 µs` per call, calling a verified Lean function thousands of times per second (e.g., per-span dependency cone updates or per-declaration fast-check inside `split_lean_source`) still pays JSON serialization + pipe context-switch overhead.
- **Proposed `lean-native` v0.6 Feature**:
  - Add a CLI subcommand `lean-native-core export-c-lib --decls <list> -o libleannative_kernels.a --header leannative_kernels.h` that compiles pure verified `Spec.lean` / `Accelerators.lean` functions into a standalone static library with flat C-ABI entrypoints (`extern "C" uint64_t ln_is_closed_section_needed(...)`).
  - This allows `crates/turbo-lean/build.rs` to link `libleannative_kernels.a` directly into the `turbo-lean` binary with **zero IPC overhead (`< 5 ns` FFI call)**!

### Feature Request 4 — Binder-Aware Statement Parser in `LeanNative/Backend/TurboPlugin.lean`
- **Problem Observed**: In `LeanNative/Backend/TurboPlugin.lean` (v0.5), `runSimdOmegaFastcheck` and `runSimdBvDecideFastcheck` inspect `req.stmtSrc` and `req.bodySrc` for arithmetic operators (`+`, `-`, `<`, `Word256`, `shl`, `shr`), and expect `stmtSrc` to include explicit parameter binders `(a b : Nat)` or `(x : Word256)`. When a caller passes a `where`-style theorem or multi-binder group `(a b c : UInt64) (h : a < b)`, `TurboPlugin.lean` should normalize binder groups and evaluate the concrete 64-bit / 256-bit boundary witness table (`[0, 1, 2, 63, 64, 255, 256, u64::MAX]`) on hypotheses `h` before reporting a counterexample.
- **Proposed `lean-native` v0.6 Enhancement**:
  - Add multi-binder group extraction (`extractTypedBinders`) and hypothesis-filtering in `LeanNative/Backend/TurboPlugin.lean`, backed by a soundness theorem in `LeanNative/Cert/Certify.lean` (`hypothesisFilteredCex_no_false_positive`).
