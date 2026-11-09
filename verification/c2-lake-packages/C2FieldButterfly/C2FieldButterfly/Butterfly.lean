import C2FieldButterfly.Field

def ditButterfly (u v tw : UInt64) : UInt64 × UInt64 :=
  let t := bbMul v tw
  (bbAdd u t, bbSub u t)

def radix4Column (a0 a1 a2 a3 tw1 tw2 tw3 : UInt64) : UInt64 × UInt64 :=
  let b0 := ditButterfly a0 a2 tw1
  let b1 := ditButterfly a1 a3 tw2
  let c0 := ditButterfly b0.1 b1.1 1
  let c1 := ditButterfly b0.2 b1.2 tw3
  (bbAdd c0.1 c1.1, bbAdd c0.2 c1.2)
