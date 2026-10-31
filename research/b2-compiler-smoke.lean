import LeanNative.Driver.CoreCLI

/-- Exercise the compiler's real command dispatcher on its own Lean 4.35 toolchain. -/
def main : IO UInt32 := do
  let r ← LeanNative.Driver.CoreCLI.dispatchSharedCommand "lean-native-core" none
    ["compile-clif", "--canonical-benchmark", "--decl", "collatz_steps"]
  return r.getD 1
