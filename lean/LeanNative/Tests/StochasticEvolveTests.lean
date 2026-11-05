import LeanNative.Core

set_option autoImplicit false

namespace LeanNative.Tests.StochasticEvolveTests

open LeanNative.IR
open LeanNative.IR.Codec
open LeanNative.Transform
open LeanNative.Driver.CoreCLI

def isOk {α ε : Type} : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def isErr {α ε : Type} : Except ε α → Bool
  | .ok _ => false
  | .error _ => true

def isOkEq {α ε : Type} [BEq α] (res : Except ε α) (expected : α) : Bool :=
  match res with
  | .ok v => v == expected
  | .error _ => false

#guard isOkEq (parseSuperoptEvolveArgs []) {
  target := .x86_64
  generations := defaultEvolveGenerations
  seed := defaultEvolveSeed
  bundleOut := none
  input := "canonical"
  json := false
}

#guard isOkEq (parseSuperoptEvolveArgs [
  "--target", "cuda_ptx",
  "--generations", "12",
  "--seed", "18446744073709551615",
  "--bundle-out", "/tmp/bundle.json",
  "--input", "canonical",
  "--json"
]) {
  target := .cuda_ptx
  generations := 12
  seed := 18446744073709551615
  bundleOut := some "/tmp/bundle.json"
  input := "canonical"
  json := true
}

#guard isErr (parseSuperoptEvolveArgs ["--target"])
#guard isErr (parseSuperoptEvolveArgs ["--target", "--json"])
#guard isErr (parseSuperoptEvolveArgs ["--target", "sparc64"])
#guard isErr (parseSuperoptEvolveArgs ["--target", "amd64"])
#guard isErr (parseSuperoptEvolveArgs ["--target", "x86_64", "--target", "arm64"])
#guard isErr (parseSuperoptEvolveArgs ["--generations"])
#guard isErr (parseSuperoptEvolveArgs ["--generations", "-1"])
#guard isErr (parseSuperoptEvolveArgs ["--generations", "01"])
#guard isErr (parseSuperoptEvolveArgs ["--generations", "4097"])
#guard isErr (parseSuperoptEvolveArgs ["--generations", "4", "--generations", "8"])
#guard isErr (parseSuperoptEvolveArgs ["--seed"])
#guard isErr (parseSuperoptEvolveArgs ["--seed", "-5"])
#guard isErr (parseSuperoptEvolveArgs ["--seed", "00"])
#guard isErr (parseSuperoptEvolveArgs ["--seed", "18446744073709551616"])
#guard isErr (parseSuperoptEvolveArgs ["--seed", "99999999999999999999999"])
#guard isErr (parseSuperoptEvolveArgs ["--seed", "1", "--seed", "2"])
#guard isErr (parseSuperoptEvolveArgs ["--bundle-out"])
#guard isErr (parseSuperoptEvolveArgs ["--bundle-out", "--json"])
#guard isErr (parseSuperoptEvolveArgs ["--bundle-out", "/tmp/a.json", "--bundle-out", "/tmp/b.json"])
#guard isErr (parseSuperoptEvolveArgs ["--input"])
#guard isErr (parseSuperoptEvolveArgs ["--input", "--json"])
#guard isErr (parseSuperoptEvolveArgs ["--input", "canonical", "--input", "canonical"])
#guard isErr (parseSuperoptEvolveArgs ["--json", "--json"])
#guard isErr (parseSuperoptEvolveArgs ["--unknown-flag"])
#guard isErr (parseSuperoptEvolveArgs ["positional.lnir"])
#guard isErr (parseSuperoptEvolveArgs ["--c-abi"])

def canonicalMod : LNIRModule := mkCanonicalBenchmarkModule

#guard isOkEq (decodeEvolveRawPayload "canon.lnir" canonicalMod.toWire) (.module canonicalMod)
#guard isOkEq (decodeEvolveRawPayload "canon.json" canonicalMod.toJson) (.module canonicalMod)

def extGood : StochasticCandidate := {
  lhs := .binOp .mul (.var 0) (.constU64 8)
  rhs := .binOp .shl (.var 0) (.constU64 3)
}

def extBad : StochasticCandidate := {
  lhs := .binOp .add (.var 0) (.constU64 1)
  rhs := .var 0
}

def extPayloadJson : String := "[" ++ extGood.toJson ++ "," ++ extBad.toJson ++ "]"

#guard isOkEq (decodeEvolveRawPayload "cands.json" extPayloadJson) (.candidates [extGood, extBad])
#guard isOkEq (decodeEvolveRawPayload "cand.json" extGood.toJson) (.candidates [extGood])

#guard isErr (decodeEvolveRawPayload "empty.json" "   ")
#guard isErr (decodeEvolveRawPayload "garbage.txt" "not-lnir-or-json")
#guard isErr (decodeEvolveRawPayload "spoof.txt" "canonical")
#guard isErr (decodeEvolveRawPayload "spoof2.txt" "LeanNative.Benchmarks.Canonical")
#guard isErr (decodeEvolveRawPayload "bad_wire.json" "{\"moduleName\":\"LeanNative.Benchmarks.Canonical\",\"wire\":\"corrupt\"}")
#guard isErr (decodeEvolveRawPayload "unclosed_wire.json" ("{\"wire\":\"" ++ canonicalMod.toWire ++ "\",\"broken\":[}"))
#guard isErr (decodeEvolveRawPayload "bad_cand.json" "[{\"lhs\":\"bad\",\"rhs\":\"bad\"}]")
#guard isErr (decodeEvolveRawPayload "empty_obj.json" "{}")
#guard isErr (decodeEvolveRawPayload "bad_syntax.json" ("{garbage,\"wire\":\"" ++ canonicalMod.toWire ++ "\"}"))
#guard isErr (decodeEvolveRawPayload "named_wire.json" "{\"wire\":\"canonical\"}")

def nestedLoopDecl : LNIRDecl := {
  name := "nested_loop_subexpr"
  params := [{ id := 0, name := "n", ty := .i64 }, { id := 1, name := "x", ty := .i64 }]
  retTy := .i64
  body :=
    .letBind 2 .i64 (.scalar (.constU64 0)) <|
    .seqFor 3 2 0 4 1 .i64
      (.letBind 5 .i64 (.scalar (.binOp .add (.binOp .mul (.var 4) (.constU64 4)) (.var 3))) (.ret 5))
      (.ret 4)
}

def nestedRoots : List ScalarExpr :=
  collectEvolutionModuleRoots { moduleName := "nested", decls := [nestedLoopDecl] }

#guard nestedRoots.contains (.binOp .mul (.var 4) (.constU64 4))
#guard nestedRoots.contains (.binOp .add (.binOp .mul (.var 4) (.constU64 4)) (.var 3))

def canonCfg : SuperoptEvolveConfig := {
  target := .arm64
  generations := 6
  seed := 1337
  bundleOut := none
  input := "canonical"
  json := true
}

def canonReceipt1 : SuperoptEvolveReceipt := executeSuperoptEvolve canonCfg (.module canonicalMod)
def canonReceipt2 : SuperoptEvolveReceipt := executeSuperoptEvolve canonCfg (.module canonicalMod)

#guard canonReceipt1 == canonReceipt2
#guard canonReceipt1.toJson == canonReceipt2.toJson
#guard canonReceipt1.rootsCollected > 0
#guard canonReceipt1.certCount > 0
#guard canonReceipt1.verifiedRulesCount == canonReceipt1.certCount
#guard canonReceipt1.moduleCostAfter < canonReceipt1.moduleCostBefore
#guard canonReceipt1.certCostAfter < canonReceipt1.certCostBefore
#guard CertifiedRuleBundle.fromJson? canonReceipt1.bundle.toJson == some canonReceipt1.bundle
#guard (StochasticJson.parse? canonReceipt1.toJson).isSome

def extReceipt : SuperoptEvolveReceipt :=
  executeSuperoptEvolve { target := .x86_64, generations := 0, seed := 7, input := "cands.json", json := true }
    (.candidates [extGood, extBad])

#guard extReceipt.inputKind == "candidates"
#guard extReceipt.externalCandidates == 2
#guard extReceipt.rejectedCandidates == 1
#guard extReceipt.certCount == 1
#guard extReceipt.verifiedRulesCount == 1
#guard extReceipt.certCostAfter < extReceipt.certCostBefore
#guard CertifiedRuleBundle.fromJson? extReceipt.bundle.toJson == some extReceipt.bundle

def parallelDecl : LNIRDecl := {
  name := "parallel_subexpr"
  params := [{ id := 0, name := "n", ty := .i64 }]
  retTy := .i64
  body := .parFor 2 0 [] .i64
    (.customScalar 1 [] (.binOp .add (.var 1) (.constU64 0))) (.ret 2)
}

def deepModule : LNIRModule := { moduleName := "deep", decls := [nestedLoopDecl, parallelDecl] }
def deepReceipt : SuperoptEvolveReceipt := executeSuperoptEvolve canonCfg (.module deepModule)

#guard deepReceipt.moduleCostAfter < deepReceipt.moduleCostBefore
#guard deepReceipt.moduleCostAfter == deepModule.decls.foldl (fun n d =>
  n + codeScalarCostWithProfile deepReceipt.bundle.profile (applyCertifiedBundleCode deepReceipt.bundle d.body)) 0
#guard deepModule.decls.all (fun d => applyCertifiedBundleCode deepReceipt.bundle d.body != d.body)
#guard applyCertsToScalar cachedStochasticBundle.profile cachedStochasticBundle.certificates
    (.select (.constBool true) stochasticCertWitnessLhs (.var 999)) ==
  .select (.constBool true) (.var 0) (.var 999)

-- Exercise the public loader, including its compressed-pack path, with exact byte hashes.
#eval show IO Unit from do
  let payload := cachedStochasticBundle.toJson.toUTF8
  let digest := TurboLean.Blake3.blake3Bytes payload
  let path := "/tmp/stochastic-evolve-integrity.tlpack"
  let compressed := path ++ ".zst"
  for tamper in [false, true] do
    let hash := if tamper then (if digest.startsWith "0" then "1" else "0") ++ digest.drop 1
      else digest
    let header := ("{\"format_version\":2,\"actions\":[],\"blobs\":[{\"size_bytes\":" ++
      toString payload.size ++ ",\"blob_hash\":\"" ++ hash ++ "\"}]}").toUTF8
    let length := ByteArray.mk ((List.range 8).map (fun i => (header.size / 256 ^ i).toUInt8)).toArray
    IO.FS.writeBinFile path (ByteArray.mk #[84, 76, 80, 75, 0, 0, 0, 2] ++ length ++ header ++ payload)
    let hasZstd ← try
      pure ((← IO.Process.output { cmd := "zstd", args := #["-q", "-f", "-o", compressed, path] }).exitCode == 0)
    catch _ => pure false
    for file in if hasZstd then [path, compressed] else [path] do
      let accepted ← try
        let _ ← loadStochasticBundleFromPath file
        pure true
      catch _ => pure false
      unless accepted != tamper do throw <| IO.userError "pack integrity regression"
  IO.FS.removeFile path
  try IO.FS.removeFile compressed catch _ => pure ()

end LeanNative.Tests.StochasticEvolveTests
