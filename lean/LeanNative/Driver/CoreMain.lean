import LeanNative.Core
import LeanNative.Proofs.AxiomAudit

open LeanNative.Driver.CoreCLI

def main (args : List String) : IO UInt32 := do
  try
    if let some rc ← dispatchSharedCommand "lean-native-core" none args then
      return rc
    match args with
    | "self-test" :: _ => runCoreSelfTest "lean-native-core"
    | "--version" :: _ | "-v" :: _ =>
      IO.println s!"lean-native-core v{LeanNative.Core.coreVersion}"
      return 0
    | "--help" :: _ | "-h" :: _ | [] =>
      printCoreUsage "lean-native-core" false
      return 0
    | cmd :: _ =>
      IO.eprintln s!"Unknown command: {cmd}"
      printCoreUsage "lean-native-core" false
      return 1
  catch e =>
    IO.eprintln s!"{e}"
    return 1
