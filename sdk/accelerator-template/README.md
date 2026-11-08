# `turbo-lean` Zero-TCB External Accelerator & `LNIR` Plugin SDK

Build, test, and benchmark external tactic accelerators, counterexample synthesizers, and `LNIR_WIRE_V1` superoptimizers in **any language** (Python, Rust, C++, Go, JAX/CUDA) **without building Lean 4**.

Every external plugin runs out-of-process over single-line JSONL `stdin`/`stdout` behind `SpeculativeGate`:
- **Tactic & Counterexample Accelerators** (`ExternalProcessAccelerator` in [`crates/turbo-lean/src/accelerators.rs`](../../crates/turbo-lean/src/accelerators.rs)): replayed through the Lean 4 kernel (`untrusted_accelerator_kernel_replay_sound`) or concrete witness evaluation; timeouts and invalid outputs fall back cleanly (`untrusted_accelerator_timeout_fallback`).
- **`LNIR` Optimization Plugins** (`runExternalOptPlugin` / `verifyOptPluginGate` in [`lean/LeanNative/Transform/Plugins.lean`](../../lean/LeanNative/Transform/Plugins.lean)): gated by symbolic translation validation (`validateTranslationDecl`, 64 steps), 64-state concrete `evalCode` equivalence, and non-increasing target cycle cost (`untrusted_opt_plugin_tv_gate_sound`).

---

## 30-Second Quickstart (Zero Lean Build Required)

```bash
# 1. Run the offline protocol, 64-state equivalence, adversarial, and timeout validator (< 1 s)
python3 sdk/accelerator-template/validate.py

# 2. Validate your own executable or script against the same fixture suite
python3 sdk/accelerator-template/validate.py --plugin-cmd "python3 plugins/verity_yul_plugin.py"
python3 sdk/accelerator-template/validate.py --plugin-cmd "./my-rust-or-cpp-plugin"

# 3. Register with `turbo-lean` via `.turbo-lean/accelerators.json` or `TURBO_LEAN_ACCELERATORS_CONFIG`
TURBO_LEAN_ACCELERATORS_CONFIG=sdk/accelerator-template/accelerators.example.json \
  turbo-lean accelerators
```

---

## Protocol 1: Tactic & Counterexample Accelerators (`ExternalProcessAccelerator`)

### Configuration (`.turbo-lean/accelerators.json` or `turbo-lean.toml`)

See [`accelerators.example.json`](./accelerators.example.json), or add to `turbo-lean.toml`:

```toml
[accelerators]
enabled = true
default_budget_ms = 25

[[accelerators.external]]
name = "plugin:sdk-template"
command = ["python3", "sdk/accelerator-template/plugin.py"]
timeout_ms = 25
trigger_tactics = [] # empty = run on all declarations; or e.g. ["simp", "omega"]
```

### Request (`stdin`, one UTF-8 JSON object + `\n`)

Matches `AcceleratorInput` in `crates/turbo-lean/src/accelerators.rs`:

```json
{"decl_name":"sdk_simp_distill","stmt_src":"(a b : Nat) (h1 : a = b) : a + 0 = b","body_src":"by simp [h1]","imports_csv":"Init","available_constants":["Nat.add_zero","h1"],"budget_ms":25}
```

### Response (`stdout`, one UTF-8 JSON line + `\n` within `min(timeout_ms, budget_ms)`)

Emit `{}` (or `null` / empty line) to abstain, or one `AcceleratorCertificate` (`#[serde(tag = "kind", rename_all = "snake_case")]`):

1. **Proof Rewrite (`rewritten_proof`)**:
   ```json
   {"kind":"rewritten_proof","new_body_src":"by simp only [Nat.add_zero, h1]","accelerator_name":"plugin:sdk-template","estimated_speedup_hint":"9.5x"}
   ```
2. **Counterexample & Hypothesis Suggestion (`counterexample_found`)**:
   ```json
   {"kind":"counterexample_found","witness_summary":"a = 0, b = 0 violates strict inequality a + b < a","suggested_hypothesis":"h_pos : 0 < b","accelerator_name":"plugin:sdk-template"}
   ```
3. **Parallel Subgoal Cuts (`subgoal_cuts`)**:
   ```json
   {"kind":"subgoal_cuts","cuts":["have h1 : n + 0 = n := by rfl","have h2 : n = n := by rfl","exact h1"],"accelerator_name":"plugin:sdk-template"}
   ```

---

## Protocol 2: `LNIR_WIRE_V1` Superoptimizer Plugins (`runExternalOptPlugin`)

### Request (`stdin`, one UTF-8 JSON object + `\n`)

Matches `runExternalOptPlugin` in `lean/LeanNative/Transform/Plugins.lean` and `LNIRModule.toWire` in `lean/LeanNative/IR/Codec.lean`:

```json
{"decl_name":"mul_two_add_zero","target":"x86_64","budget_ms":50,"wire":"LNIR_WIRE_V1|506c7567696e53696e676c65|1|D_decl|..."}
```

Supported `target` values: `"x86_64"`, `"arm64"`, `"cuda_ptx"`, `"apple_metal"`.

### Response (`stdout`, one line + `\n`)

Emit `{}` to abstain, or `{"wire":"LNIR_WIRE_V1|..."}` (raw `LNIR_WIRE_V1|...` is also accepted by `runExternalOptPlugin`). Every candidate is checked by `verifyOptPluginGate`:
1. Exact parameter `(id, ty)` and `retTy` match,
2. `validateTranslationDecl src cand 64` (UB, return domain, poison, symbolic return value, 64-state `evalCode` parity, memory writes),
3. `declScalarCost target cand <= declScalarCost target src`.

---

## Directory Contents

- [`plugin.py`](./plugin.py) — Reference zero-dependency Python 3 plugin implementing both protocols (`rewritten_proof`, `counterexample_found`, `subgoal_cuts`, and `LNIR_WIRE_V1` strength-reduction / FMA contraction / dead-`let` pruning).
- [`validate.py`](./validate.py) — Zero-Lean-build conformance suite (`AcceleratorConfig` schema, certificate schemas, 64-state `LNIR` equivalence + cost check + mutant self-test, malformed input fuzzing, and timeout kill isolation).
- [`accelerators.example.json`](./accelerators.example.json) — Ready-to-use `AcceleratorConfig` manifest.
- [`fixtures/`](./fixtures/) — Sample `tactic_requests.jsonl`, `lnir_opt_requests.jsonl`, and `adversarial_requests.jsonl`.

See [`roadmap/OPEN_CHALLENGES.md`](../../roadmap/OPEN_CHALLENGES.md) for open contributor challenges (`A1`–`A5`, `B1`–`B5`) and production plugin examples in [`plugins/`](../../plugins/).
