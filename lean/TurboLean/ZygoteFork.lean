/-
  TurboLean.ZygoteFork: Pure-Lean Interface & Sequential Fallback for Lake Builds

  The Lake library target (`lean/TurboLean/ZygoteFork.lean`) stays 100% pure Lean 4 so every
  declaration in `lean/TurboLean/` satisfies the zero-FFI / zero-axiom CI & `.olean` kernel gates.
  When `crates/turbo-lean/src/zygote.rs` compiles the cached `turbo_zygote_*` worker binary in its
  private scratch directory, it substitutes `crates/turbo-lean/src/zygote_fork_posix.lean`, wiring
  the quiesced-task-manager POSIX `fork` CoW pool over `CompactedRegion`-backed `Lean.Environment`s.
-/
import Lean.Environment

namespace TurboLean.ZygoteFork

def finalizeTaskManager : IO Unit :=
  pure ()

def initTaskManager : IO Unit :=
  pure ()

def initTaskManagerUsing (_numWorkers : UInt32) : IO Unit :=
  pure ()

def detectHardwareParallelism : IO UInt32 :=
  pure 1

def posixPipe : IO (UInt32 × UInt32) :=
  throw <| IO.userError "POSIX pipe unavailable in pure-Lean ZygoteFork build"

def posixClose (_fd : UInt32) : IO Unit :=
  pure ()

def posixForkRaw : IO UInt32 :=
  throw <| IO.userError "POSIX fork unavailable in pure-Lean ZygoteFork build"

def connectCloneChannel (_path : @& String) (_target : UInt32) : IO Unit :=
  throw <| IO.userError "POSIX clone unavailable in pure-Lean ZygoteFork build"

def reapClones (_pids : Array UInt32) : IO (Array UInt32) := pure #[]

def posixExitImmediate (_code : UInt32) : IO Unit :=
  throw <| IO.userError "POSIX exit unavailable in pure-Lean ZygoteFork build"

def posixKillSigkill (_pid : UInt32) : IO Unit :=
  pure ()

def posixWaitPid (_pid : UInt32) : IO (UInt32 × UInt32) :=
  pure (0, 0)

def posixWriteAll (_fd : UInt32) (_ba : @& ByteArray) : IO Bool :=
  pure false

def posixReadAll (_fd : UInt32) (_maxBytes : USize := 65536) : IO ByteArray :=
  pure ByteArray.empty

def waitStatusExitedZero (rawStatus : UInt32) : Bool :=
  (rawStatus &&& 0x7f) == 0 && ((rawStatus >>> 8) &&& 0xff) == 0

def raceForkConcurrency : IO Nat := do
  match ← IO.getEnv "TURBO_LEAN_RACE_FORK_JOBS" with
  | some raw =>
    match raw.trimAscii.toString.toNat? with
    | some n => return Nat.min 4 (Nat.max 1 n)
    | none => pure ()
  | none => pure ()
  let hw ← detectHardwareParallelism
  return Nat.min 4 (Nat.max 1 hw.toNat)

def isForkEnabled : IO Bool :=
  pure false

def isSingleShardForkEnabled : IO Bool :=
  pure false

def spawnQuiescedForkChild (_childWorkers : UInt32 := 2) (_childAction : IO UInt32) : IO UInt32 :=
  posixForkRaw

def runIsolatedInFork (_childWorkers : UInt32 := 2) (producePayload : IO ByteArray) : IO (Bool × ByteArray) := do
  let bytes ← producePayload
  return (true, bytes)

end TurboLean.ZygoteFork
