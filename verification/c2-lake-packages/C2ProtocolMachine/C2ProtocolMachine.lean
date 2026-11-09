import C2ProtocolMachine.Types
import C2ProtocolMachine.Transition

@[export c2_protocol_step6]
def c2_protocol_step6 (x0 : UInt64) : UInt64 :=
  let s1 := stepFrameMachine .syncWait 0 0 x0.toUInt8
  let s2 := stepFrameMachine s1.1 s1.2.1 s1.2.2 (x0 >>> 8).toUInt8
  let s3 := stepFrameMachine s2.1 s2.2.1 s2.2.2 (x0 >>> 16).toUInt8
  let s4 := stepFrameMachine s3.1 s3.2.1 s3.2.2 (x0 >>> 24).toUInt8
  let s5 := stepFrameMachine s4.1 s4.2.1 s4.2.2 (x0 >>> 32).toUInt8
  let s6 := stepFrameMachine s5.1 s5.2.1 s5.2.2 (x0 >>> 40).toUInt8
  (phaseCode s6.1 <<< 32) ||| (s6.2.1.toUInt64 <<< 16) ||| s6.2.2.toUInt64

@[export c2_usize_stencil_clamp]
def c2_usize_stencil_clamp (x0 : UInt64) : UInt64 :=
  let idx := (x0 &&& 0xFFFF).toUSize
  let cap := (((x0 >>> 16) &&& 0xFFFF) + 1).toUSize
  let left := if idx == 0 then (0 : USize) else idx - 1
  let center := if idx < cap then idx else cap - 1
  let right := if idx + 1 < cap then idx + 1 else cap - 1
  (left.toUInt64 * 3 + center.toUInt64 * 10 + right.toUInt64 * 3) / 16
