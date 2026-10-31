import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "077775ba387f1eeb2976cb8763b4633b8d5ce313"

require fv from git
  "https://github.com/eth-act/clifv.git" @ "5018b9509dc124154dbe08a5bd85862595d8eab7"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

@[default_target]
lean_lib «LeanNative» where
  globs := #[.andSubmodules `LeanNative]

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

@[default_target]
lean_exe «lean-native» where
  root := `LeanNative.Driver.Main
  supportInterpreter := true
