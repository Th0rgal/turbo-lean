import Lake
open Lake DSL

package «c2-protocol-machine» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «C2ProtocolMachine» where
  roots := #[`C2ProtocolMachine]
