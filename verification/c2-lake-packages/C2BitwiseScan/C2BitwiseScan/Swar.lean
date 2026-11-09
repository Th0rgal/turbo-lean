def rotl64Word (x : UInt64) (r : UInt64) : UInt64 :=
  let s := r &&& 63
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

def swarAddBytes64 (a b : UInt64) : UInt64 :=
  let lo := (a &&& 0x7F7F7F7F7F7F7F7F) + (b &&& 0x7F7F7F7F7F7F7F7F)
  lo ^^^ ((a ^^^ b) &&& 0x8080808080808080)

def crc32NibbleStep (crc : UInt32) (nib : UInt8) : UInt32 :=
  let c0 := crc ^^^ (nib &&& 15).toUInt32
  let c1 := if (c0 &&& 1) != 0 then (c0 >>> 1) ^^^ (0xEDB88320 : UInt32) else c0 >>> 1
  let c2 := if (c1 &&& 1) != 0 then (c1 >>> 1) ^^^ (0xEDB88320 : UInt32) else c1 >>> 1
  let c3 := if (c2 &&& 1) != 0 then (c2 >>> 1) ^^^ (0xEDB88320 : UInt32) else c2 >>> 1
  if (c3 &&& 1) != 0 then (c3 >>> 1) ^^^ (0xEDB88320 : UInt32) else c3 >>> 1
