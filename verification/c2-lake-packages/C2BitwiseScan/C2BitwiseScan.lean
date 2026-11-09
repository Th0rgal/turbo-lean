import C2BitwiseScan.Swar
import C2BitwiseScan.Scan

@[export c2_bitwise_scan_digest]
def c2_bitwise_scan_digest (x0 : UInt64) : UInt64 :=
  let tags := scanTwoBytesTagMask x0
  let crc := scanTwoBytesCrc32 x0
  let mixed := swarAddBytes64 tags (rotl64Word x0 17)
  mixed ^^^ (crc.toUInt64 <<< 32) ^^^ crc.toUInt64

@[export c2_swar_sip_mix]
def c2_swar_sip_mix (x0 : UInt64) : UInt64 :=
  let v0 := swarAddBytes64 x0 0x736F6D6570736575
  let v1 := rotl64Word (x0 ^^^ 0x646F72616E646F6D) 13 ^^^ v0
  let v2 := swarAddBytes64 (rotl64Word v0 32) v1
  rotl64Word v1 21 ^^^ v2
