import LeanNative

namespace LeanNative.Driver

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Proofs
open LeanNative.Transform
open LeanNative.Backend.LLVM
open LeanNative.Backend.GPUIR
open LeanNative.Backend.MLIRGPU
open LeanNative.Backend.Metal
open LeanNative.Backend.Hybrid
open LeanNative.Backend.FastCheck
open LeanNative.Driver.CoreCLI

def frontendHook : Option (String → IO LNIRModule) :=
  some (fun path => ingestLeanSourceFile path path)

def runBuildExe (args : List String) : IO UInt32 := do
  let inFile :=
    let explicit := findFlagValue args "--input" ""
    if !explicit.isEmpty then explicit else findFirstPositional args
  if inFile.isEmpty then
    IO.eprintln "[lean-native] Error: build-exe requires a <file.lean> input path"
    return 1
  let outBin := findFlagValue args "-o" "a.out"
  let optLevel := findFlagValue args "--opt" "-O3"
  let (optMod, lnirLlPath) ← buildNativeExecutable inFile outBin optLevel args
  IO.println s!"[lean-native] Built native executable {outBin} from {inFile} (lowered & optimized {optMod.decls.length} LCNF declarations; LNIR LLVM IR at {lnirLlPath})"
  return 0

def runAuditAxioms (args : List String) : IO UInt32 := do
  let jsonFlag := hasFlag args "--json"
  let report := verifiedAxiomAuditReport
  if jsonFlag then
    IO.println report.toJson
  else
    IO.println report.formatSummary
  return if report.passed then 0 else 1

def runTurboStatus : IO UInt32 := do
  let ok ← runFastCheckBridgeSelfTest
  IO.println s!"[lean-native] In-Process FastCheck & BLAKE3: {if ok then "PASSED" else "FAILED"}"
  return if ok then 0 else 1

def runFullSelfTest : IO UInt32 := do
  let coreRc ← runCoreSelfTest "lean-native"
  let turboOk ← runFastCheckBridgeSelfTest
  IO.println s!"15. Turbo Lean Receipt & Fast-Check: {if turboOk then "PASSED" else "FAILED"}"
  return if coreRc == 0 && turboOk then 0 else 1

unsafe def runMain (args : List String) : IO UInt32 := do
  Lean.enableInitializersExecution
  try
    if let some rc ← dispatchSharedCommand "lean-native" frontendHook args then
      return rc
    match args with
    | "build-exe" :: rest    => runBuildExe rest
    | "audit-axioms" :: rest => runAuditAxioms rest
    | "turbo-status" :: _    => runTurboStatus
    | "self-test" :: _       => runFullSelfTest
    | "--version" :: _ | "-v" :: _ =>
      IO.println s!"lean-native v{LeanNative.version}"
      return 0
    | "--help" :: _ | "-h" :: _ | [] =>
      printCoreUsage "lean-native" true
      return 0
    | cmd :: _ =>
      IO.eprintln s!"Unknown command: {cmd}"
      printCoreUsage "lean-native" true
      return 1
  catch e =>
    IO.eprintln s!"{e}"
    return 1

end LeanNative.Driver

unsafe def main (args : List String) : IO UInt32 :=
  LeanNative.Driver.runMain args
