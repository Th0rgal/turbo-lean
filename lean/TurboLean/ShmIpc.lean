/-
  TurboLean.ShmIpc: Zero-Copy `/dev/shm` Shared-Memory IPC & Payload Transport in Lean 4
  Enables `ZygoteWorker.lean` and `lean-native` workers to read/write large `prefixCode` and
  `declCode` payloads directly from `/dev/shm` (`shm:/dev/shm/...`) without hex-encoding overhead,
  and integrates `LeanSys.Store` / `LeanSys.Posix` for verified WAL/CAS and atomic file primitives.
-/
import LeanSys.Spec
import LeanSys.Posix
import LeanSys.Hash
import LeanSys.Codec
import LeanSys.Store
import LeanSys.Lsm
import LeanSys.Mmap
import LeanSys.Http
import LeanSys.Reactor
import LeanSys.Sandbox

namespace TurboLean.ShmIpc

open LeanSys.Spec
open LeanSys.Posix
open LeanSys.Hash
open LeanSys.Codec
open LeanSys.Store
open LeanSys.Lsm
open LeanSys.Mmap
open LeanSys.Http
open LeanSys.Reactor
open LeanSys.Sandbox

/-- Convert an ASCII hex character byte to its 4-bit numerical value. -/
@[inline]
def hexDigitVal (c : UInt8) : UInt8 :=
  if 48 ≤ c && c ≤ 57 then c - 48
  else if 97 ≤ c && c ≤ 102 then c - 97 + 10
  else if 65 ≤ c && c ≤ 70 then c - 65 + 10
  else 0

/-- Decode a hex-encoded UTF-8 string payload. -/
def decodeHexPayload (hex : String) : String := Id.run do
  let bytes := hex.toUTF8
  let n := bytes.size / 2
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    let hi := hexDigitVal (bytes.get! (2 * i))
    let lo := hexDigitVal (bytes.get! (2 * i + 1))
    out := out.push ((hi <<< 4) ||| lo)
  return String.fromUTF8! out

/-- Read a payload slot from `/dev/shm` (`turbo_shm_read_slot`). -/
@[export turbo_shm_read_slot]
def shmReadSlot (slotPath : String) : IO String := do
  let p : System.FilePath := slotPath
  if ← p.pathExists then
    IO.FS.readFile p
  else
    pure ""

/-- Write a payload slot to `/dev/shm` (`turbo_shm_write_slot`). -/
@[export turbo_shm_write_slot]
def shmWriteSlot (slotPath : String) (payload : String) : IO Bool := do
  try
    IO.FS.writeFile slotPath payload
    return true
  catch _ =>
    return false

/-- Persist a verified shard receipt into a `LeanSys.Store` WAL + CAS directory (`turbo_leansys_store_receipt`). -/
@[export turbo_leansys_store_receipt]
def storeShardReceiptWal (storeDir : String) (actionKey : String) (receiptJson : String) : IO Bool := do
  let .ok st0 ← openStore storeDir | return false
  let .ok st1 ← putString st0 s!"action:{actionKey}" receiptJson true | return false
  let .ok _ ← casPut st1 (ByteSlice.ofString receiptJson) | return false
  return true

/-- Decode either a `/dev/shm` slot reference (`"shm:/dev/shm/..."`) or a hex-encoded payload. -/
def decodePayloadOrShm (raw : String) : IO String := do
  if raw.startsWith "shm:" then
    let path := (raw.drop 4).toString
    shmReadSlot path
  else
    pure (decodeHexPayload raw)

end TurboLean.ShmIpc
