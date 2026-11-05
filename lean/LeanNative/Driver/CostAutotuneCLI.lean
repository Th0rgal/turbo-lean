import Lean.Data.Json
import LeanNative.IR.Codec
import LeanNative.Semantics.Eval
import LeanNative.Backend.LLVM
import LeanNative.Transform.Superopt
import LeanNative.Transform.CostAutotune

namespace LeanNative.Driver.CostAutotuneCLI

open Lean LeanNative.IR LeanNative.Semantics LeanNative.Backend LeanNative.Transform

private def operations : List String :=
  ["add", "bitwise", "shift", "cmp", "mul", "div", "fma", "select"]

private def acceptedOperations : List String := operations ++
  ["sub", "mod", "bitAnd", "bitOr", "bitXor", "shl", "shr", "sar", "eq", "lt", "le", "not", "neg",
   "add_sub", "addSub", "div_mod", "divMod", "clz256",
   "add_sub_checked256", "addSubChecked256", "mul_checked256", "mulChecked256"]

def canonicalCorpusDeclNames : List String :=
  mkCanonicalBenchmarkModule8.decls.map (·.name)

private structure Options where
  target : String := "x86_64"
  samplesPath : Option String := none
  corpusPath : Option String := none
  json : Bool := false

private def parseOptions (args : List String) : Except String Options := do
  let rec go (args : List String) (opts : Options) (seen : List String) : Except String Options := do
    match args with
    | [] => return opts
    | "--json" :: rest =>
      if seen.contains "--json" then throw "duplicate --json"
      go rest { opts with json := true } ("--json" :: seen)
    | flag :: value :: rest =>
      if flag != "--target" && flag != "--samples-json" && flag != "--corpus-json" then
        throw s!"unknown option '{flag}'"
      if seen.contains flag then throw s!"duplicate {flag}"
      if value.isEmpty || value.startsWith "-" then throw s!"{flag} requires a value"
      let opts' :=
        if flag == "--target" then { opts with target := value }
        else if flag == "--samples-json" then { opts with samplesPath := some value }
        else { opts with corpusPath := some value }
      go rest opts' (flag :: seen)
    | [flag] => throw s!"unknown option or missing value: {flag}"
  go args {} []

private def nonNegNat (j : Json) (err : String) : Except String Nat := do
  let num ← j.getNum?
  if num.exponent != 0 || num.mantissa < 0 then throw err
  return num.mantissa.toNat

private def positiveNat (j : Json) : Except String Nat := do
  let num ← j.getNum?
  if num.exponent != 0 || num.mantissa <= 0 then throw "timing values and iterations must be positive integers"
  return num.mantissa.toNat

private def parseSample (j : Json) : Except String OpTimingSample := do
  let fields ← j.getObj?
  let keys := fields.foldl (fun acc k _ => k :: acc) ([] : List String)
  if keys.length != 3 || !(keys.all (["operation", "elapsedNs", "iterations"].contains ·)) then
    throw "sample must contain exactly operation, elapsedNs, iterations"
  let operation ← (← j.getObjVal? "operation").getStr?
  if operation.isEmpty then throw "operation must not be empty"
  if !acceptedOperations.contains operation then throw s!"unsupported operation '{operation}'"
  let elapsedNs ← positiveNat (← j.getObjVal? "elapsedNs")
  let iterations ← positiveNat (← j.getObjVal? "iterations")
  return { operation, elapsedNs, iterations }

private def fieldCount (raw : String) : Nat := Id.run do
  let mut quoted := false
  let mut escaped := false
  let mut count := 0
  for c in raw.toList do
    if quoted then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == '"' then quoted := false
    else if c == '"' then quoted := true
    else if c == ':' then count := count + 1
  return count

def parseSamples (raw : String) : Except String (List OpTimingSample) := do
  let rows ← (← Json.parse raw).getArr?
  if rows.isEmpty then throw "samples array must not be empty"
  let samples ← rows.toList.mapM parseSample
  if fieldCount raw != rows.size * 3 then throw "duplicate sample fields are forbidden"
  return samples

private def parseCorpusEntry (j : Json) : Except String CorpusTimingSample := do
  let fields ← j.getObj?
  let keys := fields.foldl (fun acc k _ => k :: acc) ([] : List String)
  if keys.length != 4 || !(keys.all (["declName", "baselineNs", "candidateNs", "hits"].contains ·)) then
    throw "corpus entry must contain exactly declName, baselineNs, candidateNs, hits"
  let declName ← (← j.getObjVal? "declName").getStr?
  if !canonicalCorpusDeclNames.contains declName then
    throw s!"unknown canonical corpus declaration '{declName}'"
  let baselineNs ← positiveNat (← j.getObjVal? "baselineNs")
  let candidateNs ← positiveNat (← j.getObjVal? "candidateNs")
  let hits ← nonNegNat (← j.getObjVal? "hits") "hits must be a non-negative integer"
  return { declName, baselineNs, candidateNs, hits }

private def parseAblationEntry (j : Json) : Except String CandidateAblationSample := do
  let fields ← j.getObj?
  let keys := fields.foldl (fun acc k _ => k :: acc) ([] : List String)
  if !(keys.all (["siteIdx", "declName", "baselineNs", "soloCandidateNs", "hits", "workloadPairs"].contains ·)) then
    throw "unknown ablation entry field"
  let siteIdx ← nonNegNat (← j.getObjVal? "siteIdx") "siteIdx must be a non-negative integer"
  let declName ← (← j.getObjVal? "declName").getStr?
  if !declName.isEmpty && !canonicalCorpusDeclNames.contains declName then
    throw s!"unknown canonical corpus declaration '{declName}' in ablation"
  let baselineNs ← positiveNat (← j.getObjVal? "baselineNs")
  let soloCandidateNs ← positiveNat (← j.getObjVal? "soloCandidateNs")
  let hits ← nonNegNat (← j.getObjVal? "hits") "hits must be a non-negative integer"
  let rows ← (← j.getObjVal? "workloadPairs").getArr?
  if rows.size != canonicalCorpusDeclNames.length then
    throw "ablation workloadPairs must cover all canonical workloads"
  let workloadPairs ← rows.toList.mapM fun row => do
    let b ← positiveNat (← row.getObjVal? "baselineNs")
    let c ← positiveNat (← row.getObjVal? "soloCandidateNs")
    return (b, c)
  return { siteIdx, declName, baselineNs, soloCandidateNs, hits, workloadPairs }

private def validateAllCanonicalDecls (entries : List CorpusTimingSample) : Except String Unit := do
  if entries.length != canonicalCorpusDeclNames.length then
    throw s!"corpus must contain all {canonicalCorpusDeclNames.length} canonical declarations without duplicates"
  for name in canonicalCorpusDeclNames do
    let count := (entries.filter (fun s => s.declName == name)).length
    if count != 1 then
      throw s!"corpus missing or duplicating canonical declaration '{name}'"

/-- Imported evidence is a completed greedy leave-one-out run, not isolated-site timings.
Surviving samples must use the final corpus candidate; rejected samples describe their
elimination round. External measurements remain untrusted performance evidence. -/
def parseCorpusBundle (raw : String) :
    Except String (List CorpusTimingSample × List CandidateAblationSample) := do
  let top ← Json.parse raw
  match top.getArr? with
  | .ok rows =>
    let entries ← rows.toList.mapM parseCorpusEntry
    validateAllCanonicalDecls entries
    if fieldCount raw != rows.size * 4 then throw "duplicate corpus fields are forbidden"
    return (entries, [])
  | .error _ =>
    let fields ← top.getObj?
    let keys := fields.foldl (fun acc k _ => k :: acc) ([] : List String)
    if keys.isEmpty || !(keys.all (["corpus", "ablations"].contains ·)) || !keys.contains "corpus" then
      throw "corpus JSON object must contain corpus and optional ablations"
    let cRows ← (← top.getObjVal? "corpus").getArr?
    let entries ← cRows.toList.mapM parseCorpusEntry
    validateAllCanonicalDecls entries
    let (ablations, abFields) ←
      if keys.contains "ablations" then do
        let aRows ← (← top.getObjVal? "ablations").getArr?
        let abls ← aRows.toList.mapM parseAblationEntry
        pure (abls, 1 + aRows.size * (6 + canonicalCorpusDeclNames.length * 2))
      else pure ([], 0)
    let expectedFields := 1 + cRows.size * 4 + abFields
    if fieldCount raw != expectedFields then throw "duplicate corpus/ablation fields are forbidden"
    let finalTimes := canonicalCorpusDeclNames.map fun name =>
      ((entries.find? (fun s => s.declName == name)).getD default).candidateNs
    for s in ablations do
      if (ablations.filter (fun t => t.declName == s.declName && t.siteIdx == s.siteIdx)).length != 1 then
        throw "duplicate ablation site"
      if s.baselineNs != (s.workloadPairs.map Prod.fst).foldl (· + ·) 0 ||
          s.soloCandidateNs != (s.workloadPairs.map Prod.snd).foldl (· + ·) 0 then
        throw "ablation totals must equal workload sums"
      if candidateAblationSurvives s && s.workloadPairs.map Prod.snd != finalTimes then
        throw "surviving ablations must measure the final retained corpus candidate"
    return (entries, ablations)

#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":10}]").toOption.isSome
#guard (parseSamples "[]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":0,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":0}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":1.5,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"iterations\":10,\"extra\":1}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"add\",\"elapsedNs\":100,\"elapsedNs\":200,\"iterations\":10}]").toOption.isNone
#guard (parseSamples "[{\"operation\":\"unknown\",\"elapsedNs\":100,\"iterations\":10}]").toOption.isNone

private def sampleValidCorpusJson : String :=
  "[" ++ String.intercalate "," (canonicalCorpusDeclNames.map fun nm =>
    s!"\{\"declName\":\"{nm}\",\"baselineNs\":1000,\"candidateNs\":980,\"hits\":1}") ++ "]"

#guard (parseCorpusBundle sampleValidCorpusJson).toOption.isSome
#guard (parseCorpusBundle "[]").toOption.isNone
#guard (parseCorpusBundle "[{\"declName\":\"collatz_steps\",\"baselineNs\":1000,\"candidateNs\":980,\"hits\":1}]").toOption.isNone
#guard (parseCorpusBundle ("{\"corpus\":" ++ sampleValidCorpusJson ++
  ",\"ablations\":[{\"siteIdx\":0,\"declName\":\"collatz_steps\",\"baselineNs\":1000,\"soloCandidateNs\":980,\"hits\":1}]}")).toOption.isNone
#guard (parseCorpusBundle ("{\"corpus\":" ++ sampleValidCorpusJson ++ ",\"extra\":1}")).toOption.isNone

private def sampleAblationBundle (pairs : List (Nat × Nat)) : String :=
  let b := (pairs.map Prod.fst).foldl (· + ·) 0
  let c := (pairs.map Prod.snd).foldl (· + ·) 0
  "{\"corpus\":" ++ sampleValidCorpusJson ++
  s!",\"ablations\":[\{\"siteIdx\":0,\"declName\":\"collatz_steps\",\"baselineNs\":{b}," ++
  s!"\"soloCandidateNs\":{c},\"hits\":1,\"workloadPairs\":[" ++
  String.intercalate "," (pairs.map fun (b, c) =>
    s!"\{\"baselineNs\":{b},\"soloCandidateNs\":{c}}") ++ "]}]}"

#guard (parseCorpusBundle (sampleAblationBundle (List.replicate 8 (1000, 980)))).isOk
#guard !(parseCorpusBundle (sampleAblationBundle (List.replicate 8 (1000, 970)))).isOk
#guard [0, 1, 7, 9].all fun n =>
  !(parseCorpusBundle (sampleAblationBundle (List.replicate n (1000, 980)))).isOk
#guard [(0, 980), (1000, 0)].all fun pair =>
  !(parseCorpusBundle (sampleAblationBundle (pair :: List.replicate 7 (1000, 980)))).isOk
#guard (parseCorpusBundle (sampleAblationBundle ((10000, 9000) :: List.replicate 7 (100, 200)))).toOption.all
  (fun (_, ablations) => !keepDeclSiteByAblations ablations "collatz_steps" 8 0)
#guard ["min_gpu_elements", "minGpuElements", "gpu_block_threads", "gpuBlockThreads",
    "matmul_tile_dim", "matmulTileDim"].all fun op =>
  !(parseSamples s!"[\{\"operation\":\"{op}\",\"elapsedNs\":100,\"iterations\":1}]").isOk

@[noinline] private def runLoop (step : UInt64 → UInt64 → UInt64)
    (iterations seed : UInt64) : UInt64 := Id.run do
  let mut i : UInt64 := 0
  let mut x := seed
  while i < iterations do
    x := step x (i ||| 1)
    i := i + 1
  return x

private def operationStep : String → UInt64 → UInt64 → UInt64
  | "add" => fun x y => x + y
  | "bitwise" => fun x y => x ^^^ y
  | "shift" => fun x y => x >>> (y &&& 63)
  | "cmp" => fun x y => if x < y then 1 else 0
  | "mul" => fun x y => x * y
  | "div" => fun x y => x / y
  | "fma" => fun x y => x * y + y
  | _ => fun x y => if (x &&& 1) == 0 then y else x

private def detectHostArch : IO String := do
  let host ← IO.Process.output { cmd := "uname", args := #["-m"] }
  if host.exitCode != 0 then throw <| IO.userError "cannot establish host CPU architecture"
  return host.stdout.trimAscii.toString

private def hostMatchesTarget (target : String) (base : HardwareCostProfile) (arch : String) : IO Bool := do
  let archOk := (base.target == .x86_64 && arch == "x86_64") ||
    (base.target == .arm64 && (arch == "aarch64" || arch == "arm64"))
  if !archOk then return false
  if target == "zen5" then
    let cpu ← IO.FS.readFile "/proc/cpuinfo"
    let lines := cpu.splitOn "\n"
    let family26 := lines.any fun line => match line.splitOn ":" with
      | [key, value] => key.trimAscii.toString == "cpu family" && value.trimAscii.toString == "26"
      | _ => false
    return (cpu.contains "AuthenticAMD" && family26)
  if target == "neoverse" || target == "scaleway" then
    return false
  return true

private def checkHost (target : String) (base : HardwareCostProfile) : IO String := do
  let app ← IO.appPath
  if ["lean", "lean.exe", "lake", "lake.exe"].contains (app.fileName.getD "") then
    throw <| IO.userError "host calibration requires a compiled native executable, not lean --run"
  let arch ← detectHostArch
  let compatible := (base.target == .x86_64 && arch == "x86_64") ||
    (base.target == .arm64 && (arch == "aarch64" || arch == "arm64"))
  if !compatible then
    throw <| IO.userError s!"cannot measure target '{target}' on host '{arch}'; provide --samples-json from that hardware"
  if target == "zen5" then
    let ok ← hostMatchesTarget target base arch
    if !ok then
      throw <| IO.userError "cannot establish Zen 5 host identity; use --target x86_64 or --samples-json"
  if target == "neoverse" || target == "scaleway" then
    throw <| IO.userError s!"cannot establish preset '{target}' host identity; use --target arm64 or --samples-json"
  return arch

private def measureHost (target : String) (base : HardwareCostProfile) : IO (List OpTimingSample × Json) := do
  let arch ← checkHost target base
  let iterations : UInt64 := 2000000
  let mut checksum : UInt64 := (← IO.monoNanosNow).toUInt64 ||| 1
  let mut samples : List OpTimingSample := []
  for operation in operations do
    let step := operationStep operation
    let warm := runLoop step 10000 checksum
    let start ← IO.monoNanosNow
    let result := runLoop step iterations warm
    let stop ← IO.monoNanosNow
    checksum := checksum * 1099511628211 + result + 1
    if stop <= start then throw <| IO.userError "non-positive host timing; calibration aborted"
    samples := samples ++ [{ operation, elapsedNs := stop - start, iterations := iterations.toNat }]
  return (samples, Json.mkObj [
    ("source", .str "host_cpu_wall_clock"), ("hostArchitecture", .str arch),
    ("checksum", toJson checksum.toNat),
    ("method", .str "native UInt64 dependency-chain loops + compiled LLVM 8-kernel canonical corpus")])

private def mkDeclBenchState (declName : String) (seed : UInt64) : VarEnv × HeapState :=
  let s1 := seed + 1
  match declName with
  | "collatz_steps" =>
    (((VarEnv.empty).bind 0 (.u64 (17 + (seed &&& 7)))).bind 1 (.u64 16), HeapState.empty)
  | "tuple_accum_sum" =>
    (((VarEnv.empty).bind 0 (.u64 16)).bind 1 (.u64 s1), HeapState.empty)
  | "sarray_scale_bias" =>
    let buf : ArrayBuffer := { id := 1, exclusive := true, data := #[s1, s1 + 2, s1 + 4, s1 + 6] }
    let st : HeapState := { HeapState.empty with buffers := [buf], nextId := 1 }
    ((((VarEnv.empty).bind 0 (.sarrayId 1)).bind 1 (.u64 3)).bind 2 (.u64 5), st)
  | "dot_product_u64" | "saxpy_kernel" =>
    let b1 : ArrayBuffer := { id := 1, exclusive := true, data := #[s1, s1 + 1, s1 + 2, s1 + 3] }
    let b2 : ArrayBuffer := { id := 2, exclusive := true, data := #[2, 4, 6, 8] }
    let st : HeapState := { HeapState.empty with buffers := [b1, b2], nextId := 2 }
    (((VarEnv.empty).bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2), st)
  | "matmul_tiled_u64" =>
    let b1 : ArrayBuffer := { id := 1, exclusive := true, data := #[s1, s1 + 1, s1 + 2, s1 + 3] }
    let b2 : ArrayBuffer := { id := 2, exclusive := true, data := #[3, 5, 7, 9] }
    let b3 : ArrayBuffer := { id := 3, exclusive := true, data := #[1, 1, 1, 1] }
    let st : HeapState := { HeapState.empty with buffers := [b1, b2, b3], nextId := 3 }
    ((((VarEnv.empty).bind 0 (.sarrayId 1)).bind 1 (.sarrayId 2)).bind 2 (.sarrayId 3), st)
  | "evm_erc20_transfer_u256" =>
    let slotA := UInt256.ofUInt64 10
    let slotB := UInt256.ofUInt64 20
    let amt := UInt256.ofUInt64 (5 + (seed &&& 3))
    let sm : StorageMapBuffer := { id := 1, entries := [(slotA, UInt256.ofUInt64 1000), (slotB, UInt256.ofUInt64 250)] }
    let st : HeapState := { HeapState.empty with storageMaps := [sm], nextId := 1 }
    (((((VarEnv.empty).bind 0 (.storageMapId 1)).bind 1 (.u256 slotA)).bind 2 (.u256 slotB)).bind 3 (.u256 amt), st)
  | _ =>
    let a := UInt256.ofUInt64 (1000 + (seed &&& 15))
    let b := UInt256.ofUInt64 3000
    let w := UInt256.ofUInt64 100
    ((((VarEnv.empty).bind 0 (.u256 a)).bind 1 (.u256 b)).bind 2 (.u256 w), HeapState.empty)

private def digestDeclResult (v : Val) (st : HeapState) : Except String UInt64 := do
  match v with
  | .u64 x => return x
  | .u256 w => return w.lo0 ^^^ w.lo1 ^^^ w.hi0 ^^^ w.hi1
  | .sarrayId bid =>
    match st.findBuffer bid with
    | some buf => return buf.data.foldl (fun acc x => (acc ^^^ x) * 1099511628211) 14695981039346656037
    | none => throw s!"missing output buffer {bid}"
  | _ => throw "unexpected return value kind in canonical corpus"

def verifyAndAccumulateCorpus (baseMod candMod : LNIRModule) (iters : Nat) :
    Except String (UInt64 × UInt64) := do
  if baseMod.decls.length != canonicalCorpusDeclNames.length ||
      candMod.decls.length != canonicalCorpusDeclNames.length then
    throw "canonical corpus must contain all 8 declarations"
  let mut checksumB : UInt64 := 14695981039346656037
  let mut checksumC : UInt64 := 14695981039346656037
  for iterIdx in [:iters] do
    let iterU64 := iterIdx.toUInt64
    for (db, dc) in baseMod.decls.zip candMod.decls do
      if db.name != dc.name then
        throw s!"canonical corpus declaration order mismatch ({db.name} vs {dc.name})"
      let (env, st0) := mkDeclBenchState db.name iterU64
      match evalCode 256 env st0 db.body, evalCode 256 env st0 dc.body with
      | .ok (vb, stb), .ok (vc, stc) =>
        let hb ← digestDeclResult vb stb
        let hc ← digestDeclResult vc stc
        if hb != hc then
          throw s!"canonical corpus evaluation diverged on {db.name} at iter {iterIdx}"
        checksumB := ((checksumB ^^^ hb) * 1099511628211 ^^^ iterU64) * 1099511628211
        checksumC := ((checksumC ^^^ hc) * 1099511628211 ^^^ iterU64) * 1099511628211
      | _, _ =>
        throw s!"canonical corpus evaluation failed on {db.name} at iter {iterIdx}"
  if checksumB != checksumC then
    throw "canonical corpus rolling checksum diverged"
  return (checksumB, checksumC)

private def nativeHarnessCSource : String :=
"#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned _BitInt(256) u256_t;

typedef struct {
  u256_t keys[8];
  u256_t vals[8];
  size_t len;
} evm_map_t;

void lean_native_evm_sload(void *m_ptr, const void *slot_ptr, void *val_out) {
  evm_map_t *m = (evm_map_t *)m_ptr;
  u256_t slot;
  memcpy(&slot, slot_ptr, sizeof(u256_t));
  u256_t res = 0;
  for (size_t i = 0; i < m->len; ++i) {
    if (m->keys[i] == slot) { res = m->vals[i]; break; }
  }
  memcpy(val_out, &res, sizeof(u256_t));
}

void lean_native_evm_sstore(void *m_ptr, const void *slot_ptr, const void *val_ptr) {
  evm_map_t *m = (evm_map_t *)m_ptr;
  u256_t slot, val;
  memcpy(&slot, slot_ptr, sizeof(u256_t));
  memcpy(&val, val_ptr, sizeof(u256_t));
  for (size_t i = 0; i < m->len; ++i) {
    if (m->keys[i] == slot) { m->vals[i] = val; return; }
  }
  if (m->len < 8) { m->keys[m->len] = slot; m->vals[m->len] = val; m->len++; }
}

uint64_t lean_native_trm_matryoshka_parity_u64(uint64_t x) {
  return (uint64_t)(__builtin_popcountll(x) & 1);
}

extern uint64_t collatz_steps(uint64_t n, uint64_t steps);
extern uint64_t tuple_accum_sum(uint64_t n, uint64_t seed);
extern void *sarray_scale_bias(void *arr, uint64_t scale, uint64_t bias);
extern void *dot_product_u64(void *xs, void *ys);
extern void *saxpy_kernel(void *xs, void *ys);
extern void *matmul_tiled_u64(void *a, void *b, void *c);
extern void bench_erc20(void *out, void *m, const void *s, const void *r, const void *amt);
extern void bench_muldiv(void *out, const void *a, const void *b, const void *wad);

static u256_t evm_erc20_transfer_u256(void *m, u256_t s, u256_t r, u256_t amt) {
  u256_t out;
  bench_erc20(&out, m, &s, &r, &amt);
  return out;
}

static u256_t evm_muldiv_wad_u256(u256_t a, u256_t b, u256_t wad) {
  u256_t out;
  bench_muldiv(&out, &a, &b, &wad);
  return out;
}

static void *alloc_sarray(size_t n, uint64_t seed) {
  uint64_t *raw = (uint64_t *)malloc(24 + n * sizeof(uint64_t));
  *(int32_t *)raw = 1;
  *((int32_t *)raw + 1) = 0;
  raw[1] = (uint64_t)n;
  raw[2] = (uint64_t)n;
  for (size_t i = 0; i < n; ++i) raw[3 + i] = seed + (uint64_t)(i * 3 + 1);
  return raw;
}

static uint64_t hash_sarray(void *p) {
  uint64_t *raw = (uint64_t *)p;
  size_t n = (size_t)raw[1];
  uint64_t h = 14695981039346656037ULL;
  for (size_t i = 0; i < n; ++i) h = (h ^ raw[3 + i]) * 1099511628211ULL;
  return h;
}

static uint64_t now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(void) {
  uint64_t parity = 14695981039346656037ULL;
  for (uint64_t seed = 0; seed < 4; ++seed) {
    uint64_t results[8];
    results[0] = collatz_steps(17 + (seed & 7), 16);
    results[1] = tuple_accum_sum(16, seed + 1);
    for (int k = 2; k < 6; ++k) {
      void *a = alloc_sarray(4, 0), *b = alloc_sarray(4, 0), *c = alloc_sarray(4, 0);
      for (int i = 0; i < 4; ++i) {
        ((uint64_t *)a)[3+i] = seed + 1 + i * (k == 2 ? 2 : 1);
        ((uint64_t *)b)[3+i] = (k == 5 ? 3 : 2) + 2*i;
        ((uint64_t *)c)[3+i] = 1;
      }
      void *out = k == 2 ? sarray_scale_bias(a, 3, 5) :
        k == 3 ? dot_product_u64(a, b) : k == 4 ? saxpy_kernel(a, b) : matmul_tiled_u64(a, b, c);
      results[k] = hash_sarray(out);
      if (out != a && out != b && out != c) free(out);
      free(a); free(b); free(c);
    }
    evm_map_t mp = { .keys = {10, 20}, .vals = {1000, 250}, .len = 2 };
    u256_t words[2] = {
      evm_erc20_transfer_u256(&mp, 10, 20, 5 + (seed & 3)),
      evm_muldiv_wad_u256(1000 + (seed & 15), 3000, 100)
    };
    for (int i = 0; i < 2; ++i) {
      u256_t w = words[i];
      results[6+i] = (uint64_t)w ^ (uint64_t)(w >> 64) ^ (uint64_t)(w >> 128) ^ (uint64_t)(w >> 192);
    }
    for (int i = 0; i < 8; ++i) parity = (((parity ^ results[i]) * 1099511628211ULL) ^ seed) * 1099511628211ULL;
  }
  printf(\"PARITY_HASH %llu\\n\", (unsigned long long)parity);
  const size_t N = 256;
  uint64_t total_hash = 14695981039346656037ULL;

  {
    volatile uint64_t sink = collatz_steps(19, 64);
    uint64_t t0 = now_ns();
    uint64_t acc = 0;
    for (uint64_t i = 0; i < 4000; ++i) acc += collatz_steps(17 + (i & 7), 128);
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + acc + sink;
    printf(\"collatz_steps %llu\\n\", (unsigned long long)dt);
  }
  {
    volatile uint64_t sink = tuple_accum_sum(32, 3);
    uint64_t t0 = now_ns();
    uint64_t acc = 0;
    for (uint64_t i = 0; i < 4000; ++i) acc += tuple_accum_sum(128, i + 1);
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + acc + sink;
    printf(\"tuple_accum_sum %llu\\n\", (unsigned long long)dt);
  }
  {
    void *arr = alloc_sarray(N, 7);
    arr = sarray_scale_bias(arr, 3, 5);
    uint64_t t0 = now_ns();
    for (uint64_t i = 0; i < 2000; ++i) arr = sarray_scale_bias(arr, 3, (i & 7) + 1);
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + hash_sarray(arr);
    free(arr);
    printf(\"sarray_scale_bias %llu\\n\", (unsigned long long)dt);
  }
  {
    void *xs = alloc_sarray(N, 11);
    void *ys = alloc_sarray(N, 23);
    void *w = dot_product_u64(xs, ys);
    free(w);
    uint64_t t0 = now_ns();
    uint64_t acc = 0;
    for (uint64_t i = 0; i < 2000; ++i) {
      void *out = dot_product_u64(xs, ys);
      acc += ((uint64_t *)out)[3];
      free(out);
    }
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + acc;
    free(xs); free(ys);
    printf(\"dot_product_u64 %llu\\n\", (unsigned long long)dt);
  }
  {
    void *xs = alloc_sarray(N, 5);
    void *ys = alloc_sarray(N, 9);
    xs = saxpy_kernel(xs, ys);
    uint64_t t0 = now_ns();
    for (uint64_t i = 0; i < 2000; ++i) xs = saxpy_kernel(xs, ys);
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + hash_sarray(xs);
    free(xs); free(ys);
    printf(\"saxpy_kernel %llu\\n\", (unsigned long long)dt);
  }
  {
    void *a = alloc_sarray(N, 3);
    void *b = alloc_sarray(N, 7);
    void *c = alloc_sarray(N, 13);
    a = matmul_tiled_u64(a, b, c);
    uint64_t t0 = now_ns();
    for (uint64_t i = 0; i < 2000; ++i) a = matmul_tiled_u64(a, b, c);
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + hash_sarray(a);
    free(a); free(b); free(c);
    printf(\"matmul_tiled_u64 %llu\\n\", (unsigned long long)dt);
  }
  {
    evm_map_t mp;
    mp.len = 2;
    mp.keys[0] = (u256_t)10; mp.vals[0] = (u256_t)1000000000ULL;
    mp.keys[1] = (u256_t)20; mp.vals[1] = (u256_t)500ULL;
    (void)evm_erc20_transfer_u256(&mp, (u256_t)10, (u256_t)20, (u256_t)1);
    uint64_t t0 = now_ns();
    u256_t last = 0;
    for (uint64_t i = 0; i < 4000; ++i) {
      last = evm_erc20_transfer_u256(&mp, (u256_t)10, (u256_t)20, (u256_t)1);
    }
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + (uint64_t)last;
    printf(\"evm_erc20_transfer_u256 %llu\\n\", (unsigned long long)dt);
  }
  {
    volatile u256_t sink = evm_muldiv_wad_u256((u256_t)1000, (u256_t)3000, (u256_t)100);
    uint64_t t0 = now_ns();
    uint64_t acc = 0;
    for (uint64_t i = 0; i < 4000; ++i) {
      u256_t r = evm_muldiv_wad_u256((u256_t)(1000 + (i & 15)), (u256_t)3000, (u256_t)100);
      acc += (uint64_t)r;
    }
    uint64_t dt = now_ns() - t0;
    if (dt == 0) dt = 1;
    total_hash = total_hash * 1099511628211ULL + acc + (uint64_t)sink;
    printf(\"evm_muldiv_wad_u256 %llu\\n\", (unsigned long long)dt);
  }

  printf(\"CHECKSUM %llu\\n\", (unsigned long long)total_hash);
  return 0;
}
"

private def removeIfExists (p : System.FilePath) : IO Unit := do
  try IO.FS.removeFile p catch _ => pure ()

private def compileAndRunModuleHarness (mod : LNIRModule) (hostArch : TargetArch)
    (tag : String) : IO (List (String × Nat) × UInt64) := do
  let stamp ← IO.monoNanosNow
  let stem := s!"/tmp/turbo_lean_d4_{tag}_{stamp}"
  let llPath : System.FilePath := s!"{stem}.ll"
  let cPath : System.FilePath := s!"{stem}.c"
  let binPath : System.FilePath := s!"{stem}.bin"
  try
    let wrappers := "
define void @bench_erc20(ptr %out, ptr %m, ptr %s, ptr %r, ptr %amt) {
entry:
  %sv = load i256, ptr %s, align 1
  %rv = load i256, ptr %r, align 1
  %av = load i256, ptr %amt, align 1
  %v = call i256 @evm_erc20_transfer_u256(ptr %m, i256 %sv, i256 %rv, i256 %av)
  store i256 %v, ptr %out, align 1
  ret void
}
define void @bench_muldiv(ptr %out, ptr %a, ptr %b, ptr %wad) {
entry:
  %av = load i256, ptr %a, align 1
  %bv = load i256, ptr %b, align 1
  %wv = load i256, ptr %wad, align 1
  %v = call i256 @evm_muldiv_wad_u256(i256 %av, i256 %bv, i256 %wv)
  store i256 %v, ptr %out, align 1
  ret void
}
"
    let ir := emitLLVMOptimized mod hostArch ++ wrappers
    IO.FS.writeFile llPath ir
    IO.FS.writeFile cPath nativeHarnessCSource
    let cc ← IO.Process.output {
      cmd := "clang"
      args := #["-O2", "-Wno-override-module", llPath.toString, cPath.toString, "-o", binPath.toString]
    }
    if cc.exitCode != 0 then
      throw <| IO.userError s!"compiled corpus clang failed: {cc.stderr.trimAscii.toString}"
    let exec ← IO.Process.output { cmd := binPath.toString, args := #[] }
    if exec.exitCode != 0 then
      throw <| IO.userError s!"compiled corpus execution failed: {exec.stderr.trimAscii.toString}"
    let mut timings : List (String × Nat) := []
    let mut checksum? : Option UInt64 := none
    let mut parity? : Option UInt64 := none
    for rawLine in exec.stdout.splitOn "\n" do
      let line := rawLine.trimAscii.toString
      if !line.isEmpty then
        match line.splitOn " " with
        | ["PARITY_HASH", vStr] =>
          parity? := vStr.toNat?.map Nat.toUInt64
        | ["CHECKSUM", vStr] =>
          match vStr.toNat? with
          | some n => checksum? := some n.toUInt64
          | none => throw <| IO.userError s!"malformed harness checksum '{line}'"
        | [dName, nsStr] =>
          match nsStr.toNat? with
          | some ns => timings := timings ++ [(dName, max 1 ns)]
          | none => throw <| IO.userError s!"malformed harness timing '{line}'"
        | _ => throw <| IO.userError s!"unexpected harness output '{line}'"
    let some cs := checksum?
      | throw <| IO.userError "compiled corpus harness missing CHECKSUM"
    let (expectedParity, _) ← IO.ofExcept (verifyAndAccumulateCorpus mod mod 4)
    if parity? != some expectedParity then
      throw <| IO.userError s!"native/evalCode parity mismatch for {tag}"
    if timings.map Prod.fst != canonicalCorpusDeclNames then
      throw <| IO.userError "compiled corpus harness declaration order mismatch"
    if timings.length != canonicalCorpusDeclNames.length then
      throw <| IO.userError s!"compiled corpus harness expected 8 timings, got {timings.length}"
    removeIfExists llPath
    removeIfExists cPath
    removeIfExists binPath
    return (timings, cs)
  catch e =>
    removeIfExists llPath
    removeIfExists cPath
    removeIfExists binPath
    throw e

private def countDeclHits (recs : List SuperoptRewriteRecord) (declName : String) : Nat :=
  (recs.filter (fun r => r.declName == declName)).length

private def measureCompiledNativeCorpus (profile : HardwareCostProfile) (hostArchStr : String) :
    IO (List CorpusTimingSample × List CandidateAblationSample) := do
  let hostArch : TargetArch := if hostArchStr == "aarch64" || hostArchStr == "arm64" then .arm64 else .x86_64
  let m := mkCanonicalBenchmarkModule8
  let (baseTimings, baseHash) ← compileAndRunModuleHarness m hostArch "base"
  let sites := m.decls.flatMap fun d =>
    let (_, _, count) := superoptDeclSelective profile "" (fun _ => true) d 0
    (List.range count).map (d.name, ·)
  let (candTimings, ablations) ← ablateSitesLeaveOneOut (fun retained => do
    if retained.isEmpty then return (baseTimings.map Prod.snd, 0)
    let (retMod, retReport, _) := superoptModuleSelective profile
      (fun decl idx => retained.contains (decl, idx)) m
    let _ ← IO.ofExcept (verifyAndAccumulateCorpus m retMod 4)
    let (timings, hash) ← compileAndRunModuleHarness retMod hostArch "leave_one_out"
    if hash != baseHash then throw <| IO.userError "compiled leave-one-out checksum mismatch"
    return (timings.map Prod.snd, retReport.rewritesApplied)) sites
  let keepIdx := fun decl => keepDeclSiteByAblations ablations decl canonicalCorpusDeclNames.length
  let (_, prunedReport, _) := superoptModuleSelective profile keepIdx m
  let corpus := baseTimings.zip candTimings |>.map fun ((dName, bNs), cNs) =>
    { declName := dName, baselineNs := bNs, candidateNs := cNs,
      hits := countDeclHits prunedReport.records dName : CorpusTimingSample }
  return (corpus, ablations)

private def sampleJson (s : OpTimingSample) : Json := Json.mkObj [
  ("operation", .str s.operation), ("elapsedNs", toJson s.elapsedNs), ("iterations", toJson s.iterations)]

private def receiptJson (r : CalibrationReceipt) : Json := Json.mkObj [
  ("accepted", .bool r.accepted), ("baselineNs", toJson r.baselineNs),
  ("candidateNs", toJson r.candidateNs), ("hits", toJson r.hits),
  ("sitesConsidered", toJson r.sitesConsidered), ("sitesPruned", toJson r.sitesPruned)]

private def appendJsonFields (base : Json) (extra : List (String × Json)) : Json :=
  match base.getObj? with
  | .ok fields =>
    let existing := fields.foldl (fun acc k v => acc ++ [(k, v)]) ([] : List (String × Json))
    let filtered := existing.filter (fun (k, _) => !(extra.any (fun (ek, _) => ek == k)))
    Json.mkObj (filtered ++ extra)
  | .error _ => base

/-- Shared validation for value-taking flags in the native CLI. -/
def validateFlagValues (flags : List String) : List String → IO Unit
  | [] => return ()
  | f :: rest =>
    if !flags.contains f then validateFlagValues flags rest
    else match rest with
      | v :: tail =>
        if v.isEmpty || v.startsWith "-" then
          throw <| IO.userError s!"[lean-native] Flag '{f}' requires a valid value, got '{v}'"
        else validateFlagValues flags tail
      | [] => throw <| IO.userError s!"[lean-native] Flag '{f}' requires a value"

def run (args : List String) : IO UInt32 := do
  try
    let opts ← IO.ofExcept (parseOptions args)
    let some base := calibrationPreset opts.target
      | throw <| IO.userError s!"unknown calibration target '{opts.target}'"
    let (samples, baseProv) ← match opts.samplesPath with
      | some path => do
        let samples ← IO.ofExcept (parseSamples (← IO.FS.readFile path))
        pure (samples, Json.mkObj [("source", .str "provided_samples"), ("hostMeasured", .bool false)])
      | none => measureHost opts.target base
    let profile := calibrateHardwareProfile base samples
    let (corpus, ablations, provExtra) ← match opts.corpusPath with
      | some cPath => do
        let (cEntries, cAblations) ← IO.ofExcept (parseCorpusBundle (← IO.FS.readFile cPath))
        let (candMod, _, _) := superoptModuleSelective profile
          (fun decl => keepDeclSiteByAblations cAblations decl cEntries.length) mkCanonicalBenchmarkModule8
        let _ ← IO.ofExcept (verifyAndAccumulateCorpus mkCanonicalBenchmarkModule8 candMod 4)
        pure (cEntries, cAblations, [
          ("canonicalCorpusExecuted", .bool true),
          ("tuningMeasured", .bool true),
          ("corpusSource", .str "provided_corpus_json")])
      | none => do
        let arch ← detectHostArch
        let hostCompatible ← hostMatchesTarget opts.target base arch
        if !hostCompatible then
          pure ([], [], [
            ("canonicalCorpusExecuted", .bool false),
            ("tuningMeasured", .bool false),
            ("corpusSource", .str "none"),
            ("reason", .str "cross_target_requires_corpus_json")])
        else
          let (cEntries, cAblations) ← measureCompiledNativeCorpus profile arch
          pure (cEntries, cAblations, [
            ("canonicalCorpusExecuted", .bool true),
            ("tuningMeasured", .bool true),
            ("corpusSource", .str "compiled_llvm_native_8decl")])
    let (_, receipt) := autotuneSuperoptModule base samples corpus mkCanonicalBenchmarkModule8 ablations
    let selectedProfile := receipt.profile
    let profileJson ← IO.ofExcept (Json.parse selectedProfile.toJson)
    let measuredProfileJson ← IO.ofExcept (Json.parse profile.toJson)
    let fullProv := appendJsonFields baseProv (provExtra ++ [("measuredProfile", measuredProfileJson)])
    let report := Json.mkObj [("status", .str "calibrated"), ("target", .str opts.target),
      ("profile", profileJson), ("amdahlReceipt", receiptJson receipt),
      ("samples", .arr (samples.map sampleJson).toArray), ("provenance", fullProv)]
    if opts.json then IO.println report.compress
    else
      IO.println s!"[calibrate-cost] {opts.target}: {samples.length} timing samples; amdahlAccepted={receipt.accepted} (hits={receipt.hits}, sites={receipt.sitesConsidered}, pruned={receipt.sitesPruned}, {receipt.baselineNs}ns -> {receipt.candidateNs}ns)"
      IO.println selectedProfile.toJson
    return 0
  catch e =>
    if args.contains "--json" then
      IO.println (Json.mkObj [("status", .str "error"), ("error", .str (toString e))]).compress
    else IO.eprintln s!"[calibrate-cost] {e}"
    return 1

end LeanNative.Driver.CostAutotuneCLI
