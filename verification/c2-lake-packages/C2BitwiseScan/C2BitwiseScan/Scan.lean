import C2BitwiseScan.Swar

def classifyAsciiByte (b : UInt8) : UInt8 :=
  if b == 0x0A then 1
  else if b == 0x3A then 2
  else if b >= 0x30 then 3
  else 0

def scanTwoBytesTagMask (word : UInt64) : UInt64 :=
  let b0 := word.toUInt8
  let b1 := (word >>> 8).toUInt8
  let b2 := (word >>> 16).toUInt8
  (classifyAsciiByte b0).toUInt64 |||
  ((classifyAsciiByte b1).toUInt64 <<< 8) |||
  ((classifyAsciiByte b2).toUInt64 <<< 16)

def scanTwoBytesCrc32 (word : UInt64) : UInt32 :=
  let b0 := word.toUInt8
  let b1 := (word >>> 8).toUInt8
  let crc0 : UInt32 := 0xFFFFFFFF
  let crc1 := crc32PairStep crc0 b0
  let crc2 := crc32PairStep crc1 b1
  ~~~crc2
