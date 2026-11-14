import C2ProtocolMachine.Types
import C2ProtocolMachine.Transition

@[export c2_protocol_step6]
def c2_protocol_step6 (x0 : UInt64) : UInt64 :=
  let b0 := x0.toUInt8
  let b1 := (x0 >>> 8).toUInt8
  let p1 := stepFramePhase .syncWait b0
  let a1 := stepFrameAcc p1 0 b0
  let p2 := stepFramePhase p1 b1
  let a2 := stepFrameAcc p2 a1 b1
  (phaseCode p2 <<< 32) ||| a2.toUInt64

@[export c2_usize_stencil_clamp]
def c2_usize_stencil_clamp (x0 : UInt64) : UInt64 :=
  let idx := (x0 &&& 0xFFFF).toUSize
  let cap := (((x0 >>> 16) &&& 0xFFFF) + 1).toUSize
  let left := if idx == 0 then (0 : USize) else idx - 1
  let center := if idx < cap then idx else cap - 1
  let right := if idx + 1 < cap then idx + 1 else cap - 1
  (left.toUInt64 * 3 + center.toUInt64 * 10 + right.toUInt64 * 3) / 16
