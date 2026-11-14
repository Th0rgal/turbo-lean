def rotl64Sip (x : UInt64) (r : UInt64) : UInt64 :=
  let s := r &&& 63
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

def sipRoundV0 (v0 v1 : UInt64) : UInt64 :=
  let a0 := v0 + v1
  let b1 := rotl64Sip v1 13 ^^^ a0
  let a0' := rotl64Sip a0 32
  a0' + b1

def sipRoundV1 (v0 v1 : UInt64) : UInt64 :=
  let a0 := v0 + v1
  let b1 := rotl64Sip v1 13 ^^^ a0
  let a0' := rotl64Sip a0 32
  rotl64Sip b1 17 ^^^ (a0' + b1)

def rotl32Chacha (x : UInt32) (r : UInt32) : UInt32 :=
  let s := r &&& 31
  if s == 0 then x else (x <<< s) ||| (x >>> (32 - s))
