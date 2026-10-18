import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

lean_exe «turbo-zygote» where
  root := `TurboLean.ZygoteWorker
  supportInterpreter := true


