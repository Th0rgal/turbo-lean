import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "846dd85cd7e2677825bfe160b4a6cc17fcb38c0f"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

lean_exe «turbo-zygote» where
  root := `TurboLean.ZygoteWorker
  supportInterpreter := true


