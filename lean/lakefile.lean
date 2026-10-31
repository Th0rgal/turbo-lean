import Lake
open Lake DSL

package «turbo-lean-proofs» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require «lean-sys» from git
  "https://github.com/Th0rgal/lean-sys.git" @ "077775ba387f1eeb2976cb8763b4633b8d5ce313"

@[default_target]
lean_lib «TurboLean» where
  globs := #[.submodules `TurboLean]

@[default_target]
lean_lib «LeanNative» where
  globs := #[.andSubmodules `LeanNative]

@[default_target]
lean_lib «LeanNativeCore» where
  roots := #[`LeanNative.Core]

-- Shadow-semantics checker fixtures (scripts/check_shadow_semantics.lean --self-test).
-- Not a default target: built only by the CI self-test step (`lake build ShadowFixtures`).
lean_lib «ShadowFixtures» where
  roots := #[`ShadowFixtures]
  globs := #[.andSubmodules `ShadowFixtures]

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
