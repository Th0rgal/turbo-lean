import Lake
open Lake DSL

package «c2-field-butterfly» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «C2FieldButterfly» where
  roots := #[`C2FieldButterfly]
