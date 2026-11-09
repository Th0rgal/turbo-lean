import C2BitwiseScan.Swar

def classifyAsciiByte (b : UInt8) : UInt8 :=
  if b == 0x0A then 1
  else if b == 0x3A then 2
  else if b >= 0x30 && b <= 0x39 then 3
  else if (b >= 0x41 && b <= 0x5A) || (b >= 0x61 && b <= 0x7A) then 4
  else 0

def scanEightBytesTagMask (word : UInt64) : UInt64 × UInt32 :=
  let b0 := word.toUInt8
  let b1 := (word >>> 8).toUInt8
  let b2 := (word >>> 16).toUInt8
  let b3 := (word >>> 24).toUInt8
  let b4 := (word >>> 32).toUInt8
  let b5 := (word >>> 40).toUInt8
  let b6 := (word >>> 48).toUInt8
  let b7 := (word >>> 56).toUInt8
  let packed : UInt64 :=
    (classifyAsciiByte b0).toUInt64 |||
    ((classifyAsciiByte b1).toUInt64 <<< 8) |||
    ((classifyAsciiByte b2).toUInt64 <<< 16) |||
    ((classifyAsciiByte b3).toUInt64 <<< 24) |||
    ((classifyAsciiByte b4).toUInt64 <<< 32) |||
    ((classifyAsciiByte b5).toUInt64 <<< 40) |||
    ((classifyAsciiByte b6).toUInt64 <<< 48) |||
    ((classifyAsciiByte b7).toUInt64 <<< 56)
  let crc0 : UInt32 := 0xFFFFFFFF
  let crc1 := crc32NibbleStep (crc32NibbleStep crc0 b0) (b0 >>> 4)
  let crc2 := crc32NibbleStep (crc32NibbleStep crc1 b1) (b1 >>> 4)
  let crc3 := crc32NibbleStep (crc32NibbleStep crc2 b2) (b2 >>> 4)
  let crc4 := crc32NibbleStep (crc32NibbleStep crc3 b3) (b3 >>> 4)
  (packed, ~~~crc4)
