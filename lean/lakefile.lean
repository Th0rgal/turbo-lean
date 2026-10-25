import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "9f754f17637b68fac4f4e291a6822b8f02bace26"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

@[default_target]
lean_lib «LeanNative» where
  globs := #[.andSubmodules `LeanNative]
  leanOptions := #[⟨`autoImplicit, true⟩]

@[default_target]
lean_lib «LeanNativeCore» where
  roots := #[`LeanNative.Core]

@[default_target]
lean_exe «turbo-zygote» where
  root := `TurboLean.ZygoteWorker
  supportInterpreter := true

@[default_target]
lean_exe «turbo-lean-native» where
  root := `TurboLean.Orchestrator
  supportInterpreter := false

@[default_target]
lean_exe «lean-native-core» where
  root := `LeanNative.Driver.CoreMain
  supportInterpreter := false
