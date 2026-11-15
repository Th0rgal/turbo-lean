import C2CryptoSipHash.SipRound
import C2CryptoSipHash.Mac

@[export c2_siphash24_word]
def c2_siphash24_word (x0 : UInt64) : UInt64 :=
  sipCompressWord 0x0706050403020100 0x0F0E0D0C0B0A0908 x0

@[export c2_chacha_quarter_mix]
def c2_chacha_quarter_mix (x0 : UInt64) : UInt64 :=
  let lo := x0.toUInt32
  let hi := (x0 >>> 32).toUInt32
  chachaQuarterFold lo hi (lo ^^^ 0x61707865) (hi ^^^ 0x3320646E)
