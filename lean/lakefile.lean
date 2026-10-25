import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "7ad93dd6db5bff6762242e1131a127364bd41ba8"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

lean_exe «turbo-zygote» where
  root := `TurboLean.ZygoteWorker
  supportInterpreter := true


