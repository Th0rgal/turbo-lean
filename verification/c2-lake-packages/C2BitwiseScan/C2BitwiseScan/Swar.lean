def rotl64Word (x : UInt64) (r : UInt64) : UInt64 :=
  let s := r &&& 63
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

def swarAddBytes64 (a b : UInt64) : UInt64 :=
  let lo := (a &&& 0x7F7F7F7F7F7F7F7F) + (b &&& 0x7F7F7F7F7F7F7F7F)
  lo ^^^ ((a ^^^ b) &&& 0x8080808080808080)

def crc32PairStep (crc : UInt32) (crumb : UInt8) : UInt32 :=
  let c0 := crc ^^^ (crumb &&& 3).toUInt32
  let c1 := if (c0 &&& 1) != 0 then (c0 >>> 1) ^^^ (0xEDB88320 : UInt32) else c0 >>> 1
  if (c1 &&& 1) != 0 then (c1 >>> 1) ^^^ (0xEDB88320 : UInt32) else c1 >>> 1
