import C2FieldButterfly.Field

def ditButterflyLo (u v tw : UInt64) : UInt64 :=
  bbAdd u (bbMul v tw)

def ditButterflyHi (u v tw : UInt64) : UInt64 :=
  bbSub u (bbMul v tw)

def radix4ColumnFold (a0 a1 a2 a3 : UInt64) : UInt64 :=
  let b0Lo := ditButterflyLo a0 a2 17
  let b0Hi := ditButterflyHi a0 a2 17
  let b1Lo := ditButterflyLo a1 a3 289
  let b1Hi := ditButterflyHi a1 a3 289
  let c0 := ditButterflyLo b0Lo b1Lo 1
  let c1 := ditButterflyHi b0Hi b1Hi 4913
  (c0 <<< 32) ||| c1
