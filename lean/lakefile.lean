import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "d5faf5595d99a3b36d07a7d5cd0f10b80133453d"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

lean_exe «turbo-zygote» where
  root := `TurboLean.ZygoteWorker
  supportInterpreter := true


