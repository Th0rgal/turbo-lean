import C2ProtocolMachine.Types

def stepFramePhase (ph : FramePhase) (b : UInt8) : FramePhase :=
  match ph with
  | .syncWait => if b == 0xAA then .lenByte else .syncWait
  | .lenByte => if b == 0 then .checksumByte else .bodyStream
  | .bodyStream => if b == 0x7D then .escaped else .checksumByte
  | .escaped => .bodyStream
  | .checksumByte => if (b &&& 1) == 0 then .syncWait else .fault
  | .fault => .fault

def stepFrameAcc (ph : FramePhase) (acc : UInt16) (b : UInt8) : UInt16 :=
  match ph with
  | .syncWait => acc + 0x00AA
  | .lenByte => acc + b.toUInt16
  | .bodyStream => (acc <<< 1) ^^^ b.toUInt16
  | .escaped => acc + (b ^^^ 0x20).toUInt16
  | .checksumByte => acc ^^^ b.toUInt16
  | .fault => 0xDEAD
