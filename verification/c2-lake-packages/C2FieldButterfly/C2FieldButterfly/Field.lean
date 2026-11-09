def babyBearPrime : UInt64 := 2013265921

def bbMod (x : UInt64) : UInt64 :=
  x % babyBearPrime

def bbAdd (a b : UInt64) : UInt64 :=
  let s := bbMod a + bbMod b
  if s >= babyBearPrime then s - babyBearPrime else s

def bbSub (a b : UInt64) : UInt64 :=
  let ma := bbMod a
  let mb := bbMod b
  if ma >= mb then ma - mb else ma + babyBearPrime - mb

def bbMul (a b : UInt64) : UInt64 :=
  ((bbMod a) * (bbMod b)) % babyBearPrime

def gf2Clmul2 (a b : UInt8) : UInt16 :=
  let a16 := a.toUInt16
  let p0 := if (b &&& 1) != 0 then a16 else 0
  let p1 := if (b &&& 2) != 0 then a16 <<< 1 else 0
  p0 ^^^ p1
