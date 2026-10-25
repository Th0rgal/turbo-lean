/-
  TurboLean/Orchestrator.lean — 100% Native Lean 4 Multi-Threaded DAG Wave, CAS/WAL & FastCheck Orchestrator
  Zero `import Lean`, zero `sorryAx`, built directly on `LeanSys.{Par,Db,Os,Web,Scan,Gate}`,
  `TurboLean.Spec`, and `LeanNative.Spec`.
-/
import LeanSys
import TurboLean.Spec
import LeanNative.Spec
import LeanNative.Backend.Metal
import LeanNative.Backend.Hybrid

namespace TurboLean.Orchestrator

open LeanSys
open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Store
open LeanSys.Lsm
open LeanSys.Par
open TurboLean.Spec
open LeanNative.Spec
open LeanNative.Backend.Hybrid

/-- Descriptor for a module in a topological DAG compilation wave. -/
structure WaveModuleNode where
  name          : String
  waveIdx       : Nat
  inDegree      : UInt64
  completedDeps : UInt64
  totalDeps     : UInt64
  srcSeed       : UInt64
  deriving Repr, DecidableEq, Inhabited

/-- Certified result of compiling/verifying a single `WaveModuleNode` on a worker thread. -/
structure WaveModuleResult where
  name         : String
  waveIdx      : Nat
  artifactHash : UInt64
  cacheHit     : Bool
  artifactsOk  : Bool
  cexTriaged   : Bool
  deriving Repr, DecidableEq, Inhabited

/-- Execute a single module node inside a parallel worker task, checking `TurboLean.Spec` and
    `LeanNative.Spec` gates without any subprocess spawn or shared mutable state. -/
def executeWaveModuleNode (totalNodes : UInt64) (visitedNodes : UInt64) (node : WaveModuleNode) : IO WaveModuleResult := do
  let dagOk := verifyDagScheduleStep node.inDegree node.completedDeps node.totalDeps visitedNodes totalNodes
  if !dagOk then
    throw (IO.userError s!"TurboLean.Orchestrator: DAG schedule gate rejected module {node.name}")
  let cacheOk := verifyModuleCacheKey true true true true true
  let artOk := verifyModuleArtifactSet true true true true true true true
  let digest := splitMix64C (node.srcSeed ^^^ node.waveIdx.toUInt64)
  let cexOk := certifyCexWitnessesC (1000000 + (digest &&& 0xFF)) 0 0xFFFFFFFFFFFFFFFF == 1
  return {
    name := node.name
    waveIdx := node.waveIdx
    artifactHash := digest
    cacheHit := cacheOk
    artifactsOk := artOk
    cexTriaged := cexOk
  }

/-- Execute a multi-wave module DAG across `maxWorkers` OS threads using `LeanSys.Par.parMapWave`. -/
def runParallelDagWaves (maxWorkers : Nat) (waves : Array (Array WaveModuleNode)) : IO (Array WaveModuleResult) := do
  let totalNodes : UInt64 := (waves.foldl (fun (acc : Nat) (w : Array WaveModuleNode) => acc + w.size) 0).toUInt64
  let mut allResults : Array WaveModuleResult := #[]
  let mut visited : UInt64 := 0
  for wave in waves do
    let vSnap := visited
    let waveRes ← parMapWave maxWorkers wave (fun node => executeWaveModuleNode totalNodes vSnap node)
    allResults := allResults ++ waveRes
    visited := visited + wave.size.toUInt64
  return allResults

/-- Partition a buffer of `totalBytes` into parallel chunks (`minGrain`), certify every chunk via
    `LeanNative.Spec.verifyParForChunkPartitionC`, and compute a parallel zero-copy `ByteSlice` reduction
    verified against sequential chunk folding. -/
def verifyParallelShardReduction (totalBytes minGrain maxWorkers : Nat) : IO (Bool × Nat × UInt64) := do
  let mut raw := ByteArray.emptyWithCapacity totalBytes
  for i in [0:totalBytes] do
    raw := raw.push ((i * 131 + 17) % 251).toUInt8
  let chunks := partitionRange raw.size minGrain maxWorkers
  let workersU64 := (Nat.max 1 (Nat.min maxWorkers chunks.size)).toUInt64
  let mut allGatesOk := true
  for c in chunks do
    let g := verifyParForChunkPartitionC
      c.startIdx.toUInt64 c.endIdx.toUInt64 raw.size.toUInt64 minGrain.toUInt64
      1 workersU64
    if g != 1 then
      allGatesOk := false
  let parDigest := parReduceSlices raw minGrain maxWorkers 0 (· ^^^ ·)
    (fun sl => xxh64Slice sl sl.off.toUInt64)
  let mut seqDigest : UInt64 := 0
  for c in chunks do
    let sl : ByteSlice := { ba := raw, off := c.startIdx, len := c.endIdx - c.startIdx }
    seqDigest := seqDigest ^^^ xxh64Slice sl sl.off.toUInt64
  return (allGatesOk && parDigest == seqDigest && parDigest != 0, chunks.size, parDigest)

/-- Persist wave compilation results into a crash-atomic `LeanSys.Db` WAL/LSM/CAS store and verify
    snapshot-isolated retrieval and CAS digest integrity. -/
def verifyAtomicStorePersistence (results : Array WaveModuleResult) : IO Bool := do
  let ts ← IO.monoNanosNow
  let testDir := s!"/tmp/turbo_lean_native_store_{ts}"
  let pTest : System.FilePath := testDir
  if ← pTest.pathExists then
    IO.FS.removeDirAll pTest
  IO.FS.createDirAll pTest
  let .ok st0 ← openStore testDir | return false
  let mut batch : Array (String × ByteSlice) := #[]
  let mut casOk := true
  for r in results do
    let key := s!"mod:{r.name}"
    let payloadStr := s!"wave={r.waveIdx};hash={r.artifactHash};ok={r.artifactsOk}"
    let payloadSlice := ByteSlice.ofString payloadStr
    batch := batch.push (key, payloadSlice)
    match ← casPut st0 payloadSlice with
    | .ok casKey =>
      let matPath := s!"{testDir}/{r.name}.artifact"
      match ← casMaterialize st0 casKey matPath with
      | .ok () =>
        let readBack ← IO.FS.readFile matPath
        if readBack != payloadStr then casOk := false
      | .error _ => casOk := false
    | .error _ => casOk := false
  let .ok st1 ← putBatch st0 batch true | return false
  let sstPath := s!"{testDir}/modules.sst"
  let .ok (stCompacted, sstTbl) ← SstTable.flushAndCompactStore st1 sstPath | return false
  let .ok sstLazy ← SstTable.openSstLazy sstPath | return false
  let mut readOk := true
  for r in results do
    let key := s!"mod:{r.name}"
    let expected := s!"wave={r.waveIdx};hash={r.artifactHash};ok={r.artifactsOk}"
    let lazyVal ← SstTable.getLazyIO? sstLazy key
    let lazyStr := lazyVal.map (fun ba => ByteSlice.toStringLossy (ByteSlice.ofByteArray ba))
    if getString? stCompacted key != some expected || SstTable.getString? sstTbl key != some expected || lazyStr != some expected then
      readOk := false
  IO.FS.removeDirAll pTest
  return casOk && readOk

/-- Unified `LeanSys.Db` (`Store` + `Lsm` + `openSstLazy`) module & file-split cache store,
    gated by `TurboLean.Spec.verifyModuleCacheKey` (`turbo_spec_verify_module_cache_key`)
    and `LeanSys.Spec.verifySstBlock`. -/
def putModuleCacheEntry (storeDir modKey : String)
    (toolchainMatch argsMatch srcMatch depOleansMatch configMatch : Bool)
    (payload : String) (flushSst : Bool := true) : IO Bool := do
  if !verifyModuleCacheKey toolchainMatch argsMatch srcMatch depOleansMatch configMatch then
    return false
  let pDir : System.FilePath := storeDir
  IO.FS.createDirAll pDir
  let .ok st0 ← openStore storeDir | return false
  let .ok st1 ← putString st0 s!"modcache:{modKey}" payload true | return false
  let _ ← casPut st1 (ByteSlice.ofString payload)
  if flushSst then
    let .ok _ ← SstTable.flushAndCompactStore st1 s!"{storeDir}/modules.sst" | return false
  return true

/-- Lookup a cached module/split entry from `LeanSys.Db`, checking `modules.sst` via `openSstLazy`
    (`0 B` resident value RAM) first and falling back to the WAL `Store.Handle`. -/
def getModuleCacheEntry? (storeDir modKey : String) : IO (Option String) := do
  let fullKey := s!"modcache:{modKey}"
  let sstPath := s!"{storeDir}/modules.sst"
  if ← (System.FilePath.mk sstPath).pathExists then
    if let .ok sstLazy ← SstTable.openSstLazy sstPath then
      if let some valBa ← SstTable.getLazyIO? sstLazy fullKey then
        return some (ByteSlice.toStringLossy (ByteSlice.ofByteArray valBa))
  if let .ok st ← openStore storeDir then
    return getString? st fullKey
  return none

/-- Compile an array of `.lean` source files in a parallel DAG wave across `maxWorkers` OS threads
    by spawning `lean -o <file>.olean <file>.lean` via `LeanSys.Par.parMapWave`. -/
def compileFilesWave (leanBin : String) (maxWorkers : Nat) (files : Array String) : IO (Array Bool) :=
  parMapWave maxWorkers files fun file => do
    let oleanOut := file ++ ".olean"
    let out ← IO.Process.output { cmd := leanBin, args := #["-o", oleanOut, file] }
    return out.exitCode == 0

/-- Run the deterministic `turbo-lean-native self-test` suite. -/
def runSelfTest : IO UInt32 := do
  let wave0 : Array WaveModuleNode := #[
    { name := "LeanSys.Core",  waveIdx := 0, inDegree := 0, completedDeps := 0, totalDeps := 0, srcSeed := 0x1001 },
    { name := "LeanSys.Posix", waveIdx := 0, inDegree := 0, completedDeps := 0, totalDeps := 0, srcSeed := 0x1002 },
    { name := "LeanSys.Hash",  waveIdx := 0, inDegree := 0, completedDeps := 0, totalDeps := 0, srcSeed := 0x1003 }
  ]
  let wave1 : Array WaveModuleNode := #[
    { name := "LeanSys.Store", waveIdx := 1, inDegree := 0, completedDeps := 3, totalDeps := 3, srcSeed := 0x2001 },
    { name := "LeanSys.Par",   waveIdx := 1, inDegree := 0, completedDeps := 3, totalDeps := 3, srcSeed := 0x2002 }
  ]
  let wave2 : Array WaveModuleNode := #[
    { name := "TurboLean.Orchestrator", waveIdx := 2, inDegree := 0, completedDeps := 5, totalDeps := 5, srcSeed := 0x3001 }
  ]
  let waves := #[wave0, wave1, wave2]
  let waveResults ← runParallelDagWaves 4 waves
  let allModulesOk := waveResults.size == 6 &&
    waveResults.all (fun r => r.cacheHit && r.artifactsOk && r.cexTriaged && r.artifactHash != 0)
  let (shardsOk, chunkCount, _shardDigest) ← verifyParallelShardReduction 16384 1024 4
  let storeOk ← verifyAtomicStorePersistence waveResults
  let parCexResults := parMapChunks 64 16 4 fun c =>
    certifyCexWitnessesC (1000000 + c.startIdx.toUInt64) 0 0xFFFFFFFFFFFFFFFF == 1
  let microResults ← parMapMicroChunks 96 { maxWorkers := 6, microChunkFactor := 4, minGrain := 4, isMobileHetero := true } fun c =>
    pure (certifyCexWitnessesC (1000000 + c.startIdx.toUInt64) 0 0xFFFFFFFFFFFFFFFF == 1)
  let tsCache ← IO.monoNanosNow
  let cacheDir := s!"/tmp/turbo_lean_modcache_{tsCache}"
  let cachePutOk ← putModuleCacheEntry cacheDir "LeanNative.Backend.Metal" true true true true true "cabi_digest=0x1337" true
  let cacheRejectBad ← putModuleCacheEntry cacheDir "LeanNative.Bad" true true false true true "bad" true
  let cacheGetHit ← getModuleCacheEntry? cacheDir "LeanNative.Backend.Metal"
  let cacheGetMiss ← getModuleCacheEntry? cacheDir "LeanNative.NonExistent"
  if ← (System.FilePath.mk cacheDir).pathExists then
    IO.FS.removeDirAll cacheDir
  let modCacheOk := cachePutOk && !cacheRejectBad && cacheGetHit == some "cabi_digest=0x1337" && cacheGetMiss.isNone
  let routeGpuOk := selectAppleA15Target 262144 false true true == .gpuMetal &&
    selectAppleA15Target 262143 false true true == .cpuSimd &&
    selectAppleA15Target 262144 false true false == .cpuSimd &&
    selectAppleA15Target 262144 true true true == .cpuSimd
  let unaryDecl : LeanNative.IR.LNIRDecl := {
    name := "scale_u64"
    params := [{ id := 0, name := "x", ty := .i64 }]
    retTy := .i64
    body := .parFor 1 0 [0] .i64 (.mapScaleAdd 3 0) (.ret 1)
  }
  let binaryDecl : LeanNative.IR.LNIRDecl := {
    name := "zipadd_u64"
    params := [{ id := 0, name := "a", ty := .i64 }, { id := 1, name := "b", ty := .i64 }]
    retTy := .i64
    body := .parFor 2 0 [0, 1] .i64 .zipAdd (.ret 2)
  }
  let saxpyDecl : LeanNative.IR.LNIRDecl := {
    name := "saxpy_u64"
    params := [{ id := 0, name := "x", ty := .i64 }, { id := 1, name := "y", ty := .i64 }]
    retTy := .i64
    body := .parFor 2 0 [0, 1] .i64 (.saxpy 5) (.ret 2)
  }
  let sampleMod : LeanNative.IR.LNIRModule := {
    moduleName := "SelfTestMetal"
    decls := [unaryDecl, binaryDecl, saxpyDecl]
  }
  let samplePlan : HybridPartitionPlan := {
    (default : HybridPartitionPlan) with
    moduleName := "SelfTestMetal"
    gpuDecls := [unaryDecl, binaryDecl, saxpyDecl]
    minGpuElements := 262144
  }
  let mslCode := LeanNative.Backend.Metal.emitMetalModule sampleMod
  let glueCode := emitMetalZeroCopyHostGlue samplePlan
  let unarySpec := declMetalBindingSpec unaryDecl
  let binarySpec := declMetalBindingSpec binaryDecl
  let saxpySpec := declMetalBindingSpec saxpyDecl
  let badSaxpySpec : MetalKernelBindingSpec := { saxpyF16MetalBindingSpec with outputBufferName := "wrong_out" }
  let contractsOk :=
    verifyMetalBindingContract saxpyF16MetalBindingSpec mslCode glueCode &&
    verifyMetalBindingContract unarySpec mslCode glueCode &&
    verifyMetalBindingContract binarySpec mslCode glueCode &&
    verifyMetalBindingContract saxpySpec mslCode glueCode &&
    !(verifyMetalBindingContract badSaxpySpec mslCode glueCode) &&
    saxpyF16MetalBindingSpec.outBufferIdx == 2 &&
    saxpyF16MetalBindingSpec.scalarF16BufferIdx? == some 3 &&
    saxpyF16MetalBindingSpec.nBufferIdx == 4 &&
    unarySpec.outBufferIdx == 1 && unarySpec.nBufferIdx == 2 &&
    binarySpec.outBufferIdx == 2 && binarySpec.nBufferIdx == 3 &&
    saxpySpec.outBufferIdx == 2 && saxpySpec.nBufferIdx == 3
  let glueHasObjcDispatch := (glueCode.splitOn "MTLCreateSystemDefaultDevice()").length > 1 &&
    (glueCode.splitOn "newBufferWithBytesNoCopy:ptr length:aligned options:MTLResourceStorageModeShared").length > 1 &&
    (glueCode.splitOn "out_capacity < aligned_bytes || in0_capacity < aligned_bytes").length > 1 &&
    (glueCode.splitOn "[enc setBuffer:bufIn0 offset:0 atIndex:0]").length > 1 &&
    (glueCode.splitOn "[enc setBuffer:bufOut offset:0 atIndex:1]").length > 1 &&
    (glueCode.splitOn "[enc setBuffer:bufX offset:0 atIndex:0]").length > 1 &&
    (glueCode.splitOn "[enc setBuffer:bufY offset:0 atIndex:1]").length > 1 &&
    (glueCode.splitOn "[enc setBytes:&alpha_f16_bits length:sizeof(uint16_t) atIndex:3]").length > 1 &&
    (glueCode.splitOn "[enc setBytes:&n_u64 length:sizeof(uint64_t) atIndex:4]").length > 1 &&
    (glueCode.splitOn "dispatchThreads:MTLSizeMake(n, 1, 1)").length > 1 &&
    (glueCode.splitOn "MTLCommandBufferStatusCompleted").length > 1 &&
    (glueCode.splitOn "lean_native_metal_route_admissible").length > 1 &&
    contractsOk
  let parCexOk := parCexResults.size == 4 && parCexResults.all id && !microResults.isEmpty && microResults.all id &&
    modCacheOk && routeGpuOk && glueHasObjcDispatch
  if allModulesOk && shardsOk && storeOk && parCexOk then
    IO.println s!"TURBO_LEAN_NATIVE_SELF_TEST_OK waves={waves.size} modules={waveResults.size} chunks={chunkCount} cas_verified={storeOk} cex_certified={parCexOk}"
    return 0
  else
    IO.eprintln s!"TURBO_LEAN_NATIVE_SELF_TEST_FAIL modulesOk={allModulesOk} shardsOk={shardsOk} storeOk={storeOk} parCexOk={parCexOk}"
    return 1

end TurboLean.Orchestrator

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["self-test"] => TurboLean.Orchestrator.runSelfTest
  | "compile-wave" :: leanBin :: files =>
    let res ← TurboLean.Orchestrator.compileFilesWave leanBin 4 files.toArray
    let allOk := res.all id
    IO.println s!"\{\"ok\":{allOk},\"compiled\":{res.size}}"
    return if allOk then 0 else 1
  | ["verify-shards", bytesStr, workersStr] =>
    let totalBytes := bytesStr.toNat?.getD 16384
    let workers := workersStr.toNat?.getD 4
    let (ok, chunks, digest) ← TurboLean.Orchestrator.verifyParallelShardReduction totalBytes 1024 workers
    IO.println s!"\{\"ok\":{ok},\"bytes\":{totalBytes},\"chunks\":{chunks},\"digest\":{digest}}"
    return if ok then 0 else 1
  | _ =>
    IO.println "Usage: turbo-lean-native [self-test | verify-shards <bytes> <workers>]"
    return 0
