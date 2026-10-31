import Lake
open Lake DSL
package fixture where
  leanOptions := #[⟨`debug.skipKernelTC, true⟩]
@[default_target]
lean_lib Bad
