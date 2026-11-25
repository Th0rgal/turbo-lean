import Lake
open Lake DSL

package «c2-batteries-driver» where
  leanOptions := #[⟨`autoImplicit, false⟩]

/- Tier C2 external ecosystem pin, declared as (repo_url, commit_sha,
lean_toolchain): commit `66e469188fe07963e5cf666c7d4433f45b8131c5` is upstream
tag `v4.35.0`, whose `lean-toolchain` is `leanprover/lean4:v4.35.0` (this
package's own `lean-toolchain`). `scripts/run_conformance_suite.py`
(`C2_EXTERNAL_DEPS`) provisions exactly this pin with `lake build
Batteries:static` and fails closed when this `require` and its pin diverge. -/
require batteries from git
  "https://github.com/leanprover-community/batteries" @ "66e469188fe07963e5cf666c7d4433f45b8131c5"

@[default_target]
lean_lib «C2BatteriesDriver» where
  roots := #[`C2BatteriesDriver]
