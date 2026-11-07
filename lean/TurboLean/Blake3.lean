/-
  TurboLean.Blake3 — Shared RFC-compliant pure Lean 4 BLAKE3 (256-bit hex digest).
  Zero `import Lean`: usable from both `LeanNative` (`lean-native-core`) and `TurboLean` (`ZygoteWorker`).
-/
namespace TurboLean.Blake3

def IV : Array UInt32 := #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]
def MSG_PERMUTATION : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
def CHUNK_START : UInt32 := 1
def CHUNK_END   : UInt32 := 2
def PARENT      : UInt32 := 4
def ROOT        : UInt32 := 8

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

@[inline] def g (state : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 :=
  let va := state[a]! + state[b]! + mx; let vd := rotr32 (state[d]! ^^^ va) 16
  let vc := state[c]! + vd; let vb := rotr32 (state[b]! ^^^ vc) 12
  let va := va + vb + my; let vd := rotr32 (vd ^^^ va) 8
  let vc := vc + vd; let vb := rotr32 (vb ^^^ vc) 7
  (((state.set! a va).set! b vb).set! c vc).set! d vd

@[inline] def roundFn (state : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let state := g (g (g (g state 0 4 8 12 m[0]! m[1]!) 1 5 9 13 m[2]! m[3]!) 2 6 10 14 m[4]! m[5]!) 3 7 11 15 m[6]! m[7]!
  g (g (g (g state 0 5 10 15 m[8]! m[9]!) 1 6 11 12 m[10]! m[11]!) 2 7 8 13 m[12]! m[13]!) 3 4 9 14 m[14]! m[15]!

@[inline] def permute (m : Array UInt32) : Array UInt32 := MSG_PERMUTATION.map (fun idx => m[idx]!)

def compress (cv : Array UInt32) (blockWords : Array UInt32) (counter : UInt64) (blockLen : UInt32) (flags : UInt32) : Array UInt32 :=
  let st0 : Array UInt32 := #[cv[0]!, cv[1]!, cv[2]!, cv[3]!, cv[4]!, cv[5]!, cv[6]!, cv[7]!,
    IV[0]!, IV[1]!, IV[2]!, IV[3]!, counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let (st, _) := (List.range 7).foldl (fun (st, m) r => (roundFn st m, if r < 6 then permute m else m)) (st0, blockWords)
  (List.range 8).foldl (fun acc i => (acc.set! i (acc[i]! ^^^ acc[i + 8]!)).set! (i + 8) (acc[i + 8]! ^^^ cv[i]!)) st

def blockBytesToWords (bytes : ByteArray) (offset : Nat) (len : Nat) : Array UInt32 :=
  let getByte (k : Nat) : UInt32 := if k < len && offset + k < bytes.size then (bytes.get! (offset + k)).toUInt32 else 0
  (Array.range 16).map (fun w =>
    let base := w * 4
    getByte base ||| (getByte (base + 1) <<< 8) ||| (getByte (base + 2) <<< 16) ||| (getByte (base + 3) <<< 24))

def wordToHexLE (w : UInt32) : String :=
  let hexChars := "0123456789abcdef".toList
  let byteHex (b : UInt32) : List Char := [hexChars[((b >>> 4) &&& 0xf).toNat]?.getD '0', hexChars[(b &&& 0xf).toNat]?.getD '0']
  String.ofList (byteHex (w &&& 0xff) ++ byteHex ((w >>> 8) &&& 0xff) ++ byteHex ((w >>> 16) &&& 0xff) ++ byteHex ((w >>> 24) &&& 0xff))

def cvToHex (cv : Array UInt32) : String := String.join ((List.range 8).map (fun i => wordToHexLE cv[i]!))

def hashChunk (bytes : ByteArray) (chunkOffset : Nat) (chunkLen : Nat) (chunkCounter : UInt64) (isRoot : Bool) : Array UInt32 :=
  let numBlocks := if chunkLen == 0 then 1 else (chunkLen + 63) / 64
  (List.range numBlocks).foldl (fun cv bIdx =>
    let blkOffset := chunkOffset + bIdx * 64
    let blkLen := if chunkLen == 0 then 0 else Nat.min 64 (chunkLen - bIdx * 64)
    let flags : UInt32 := (if bIdx == 0 then CHUNK_START else 0) ||| (if bIdx + 1 == numBlocks then CHUNK_END ||| (if isRoot then ROOT else 0) else 0)
    (compress cv (blockBytesToWords bytes blkOffset blkLen) chunkCounter blkLen.toUInt32 flags).extract 0 8) IV

def mergeStack (fuel : Nat) (stack : List (Array UInt32)) (count : Nat) (isFinalChunk : Bool) : List (Array UInt32) :=
  match fuel with
  | 0 => stack
  | fuel' + 1 =>
    if count % 2 == 1 then stack
    else match stack with
      | rightCv :: leftCv :: rest =>
        let flags := PARENT ||| (if isFinalChunk && rest.isEmpty && (count / 2 == 1) then ROOT else 0)
        mergeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest) (count / 2) isFinalChunk
      | _ => stack

def finalizeStack (fuel : Nat) (stack : List (Array UInt32)) : Array UInt32 :=
  match fuel, stack with
  | 0, _ => stack.head?.getD IV
  | _, [] => IV
  | _, [rootCv] => rootCv
  | fuel' + 1, rightCv :: leftCv :: rest =>
    let flags := PARENT ||| (if rest.isEmpty then ROOT else 0)
    finalizeStack fuel' (((compress IV (leftCv ++ rightCv) 0 64 flags).extract 0 8) :: rest)

def blake3Bytes (bytes : ByteArray) : String :=
  let totalLen := bytes.size
  let numChunks := if totalLen == 0 then 1 else (totalLen + 1023) / 1024
  if numChunks == 1 then cvToHex (hashChunk bytes 0 totalLen 0 true)
  else
    let stack := (List.range numChunks).foldl (fun st cIdx =>
      let cOff := cIdx * 1024
      let cLen := Nat.min 1024 (totalLen - cOff)
      let cv := hashChunk bytes cOff cLen cIdx.toUInt64 false
      mergeStack 64 (cv :: st) (cIdx + 1) (cIdx + 1 == numChunks)) []
    cvToHex (finalizeStack 64 stack)

def blake3Hex (s : String) : String := blake3Bytes s.toUTF8

end TurboLean.Blake3
