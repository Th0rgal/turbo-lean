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

def gf2Clmul8 (a b : UInt8) : UInt16 :=
  let a16 := a.toUInt16
  let p0 := if (b &&& 1) != 0 then a16 else 0
  let p1 := if (b &&& 2) != 0 then a16 <<< 1 else 0
  let p2 := if (b &&& 4) != 0 then a16 <<< 2 else 0
  let p3 := if (b &&& 8) != 0 then a16 <<< 3 else 0
  let p4 := if (b &&& 16) != 0 then a16 <<< 4 else 0
  let p5 := if (b &&& 32) != 0 then a16 <<< 5 else 0
  let p6 := if (b &&& 64) != 0 then a16 <<< 6 else 0
  let p7 := if (b &&& 128) != 0 then a16 <<< 7 else 0
  p0 ^^^ p1 ^^^ p2 ^^^ p3 ^^^ p4 ^^^ p5 ^^^ p6 ^^^ p7
