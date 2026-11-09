import C2FieldButterfly.Field
import C2FieldButterfly.Butterfly

@[export c2_babybear_radix4]
def c2_babybear_radix4 (x0 : UInt64) : UInt64 :=
  let a0 := x0 &&& 0xFFFFFFFF
  let a1 := x0 >>> 32
  let a2 := bbAdd a0 1337
  let a3 := bbSub a1 42
  radix4ColumnFold a0 a1 a2 a3

@[export c2_gf2_clmul_tower]
def c2_gf2_clmul_tower (x0 : UInt64) : UInt64 :=
  let p0 := gf2Clmul2 x0.toUInt8 ((x0 >>> 8).toUInt8 &&& 3)
  let p1 := gf2Clmul2 (x0 >>> 16).toUInt8 ((x0 >>> 24).toUInt8 &&& 3)
  let p2 := gf2Clmul2 (x0 >>> 32).toUInt8 ((x0 >>> 40).toUInt8 &&& 3)
  p0.toUInt64 ||| (p1.toUInt64 <<< 16) ||| (p2.toUInt64 <<< 32)
