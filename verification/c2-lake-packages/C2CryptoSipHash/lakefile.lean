import Lake
open Lake DSL

package «c2-crypto-siphash» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «C2CryptoSipHash» where
  roots := #[`C2CryptoSipHash]
