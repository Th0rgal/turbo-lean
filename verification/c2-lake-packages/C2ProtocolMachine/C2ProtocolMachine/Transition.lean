import C2ProtocolMachine.Types

def stepFrameMachine (ph : FramePhase) (rem : UInt8) (acc : UInt16) (b : UInt8) : FramePhase × (UInt8 × UInt16) :=
  match ph with
  | .syncWait =>
    if b == 0xAA then (.lenByte, (0, 0x00AA)) else (.syncWait, (0, acc))
  | .lenByte =>
    if b == 0 then (.checksumByte, (0, acc ^^^ 0x00FF))
    else if b > 32 then (.fault, (0, 0xDEAD))
    else (.bodyStream, (b, acc + b.toUInt16))
  | .bodyStream =>
    if b == 0x7D then (.escaped, (rem, acc ^^^ 0x007D))
    else if rem <= 1 then (.checksumByte, (0, (acc <<< 1) ^^^ b.toUInt16))
    else (.bodyStream, (rem - 1, (acc <<< 1) ^^^ b.toUInt16))
  | .escaped =>
    let unesc := b ^^^ 0x20
    if rem <= 1 then (.checksumByte, (0, (acc + unesc.toUInt16) ^^^ 0x55AA))
    else (.bodyStream, (rem - 1, acc + unesc.toUInt16))
  | .checksumByte =>
    if (acc.toUInt8 ^^^ b) == 0 then (.syncWait, (0, acc + 1))
    else (.fault, (0, acc ^^^ b.toUInt16))
  | .fault =>
    if b == 0xAA then (.lenByte, (0, 0x00AA)) else (.fault, (rem, acc))
