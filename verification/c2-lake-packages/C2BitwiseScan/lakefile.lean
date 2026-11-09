import Lake
open Lake DSL

package «c2-bitwise-scan» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «C2BitwiseScan» where
  roots := #[`C2BitwiseScan]
