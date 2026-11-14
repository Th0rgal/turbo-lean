import C2CryptoSipHash.SipRound

def sipCompressWord (k0 k1 msg : UInt64) : UInt64 :=
  let v0 := k0 ^^^ 0x736F6D6570736575
  let v1 := (k1 ^^^ 0x646F72616E646F6D) ^^^ msg
  let r1v0 := sipRoundV0 v0 v1
  let r1v1 := sipRoundV1 v0 v1
  let r2v0 := sipRoundV0 (r1v0 ^^^ msg) (r1v1 ^^^ 0xFF)
  let r2v1 := sipRoundV1 (r1v0 ^^^ msg) (r1v1 ^^^ 0xFF)
  r2v0 ^^^ r2v1

def chachaQuarterFold (a b c d : UInt32) : UInt64 :=
  let a1 := a + b
  let d1 := rotl32Chacha (d ^^^ a1) 16
  let c1 := c + d1
  let b1 := rotl32Chacha (b ^^^ c1) 12
  let a2 := a1 + b1
  let d2 := rotl32Chacha (d1 ^^^ a2) 8
  let c2 := c1 + d2
  let b2 := rotl32Chacha (b1 ^^^ c2) 7
  ((a2 ^^^ c2).toUInt64 <<< 32) ||| (b2 ^^^ d2).toUInt64
