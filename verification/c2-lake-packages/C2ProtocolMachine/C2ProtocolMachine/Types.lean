inductive FramePhase where
  | syncWait
  | lenByte
  | bodyStream
  | escaped
  | checksumByte
  | fault

def phaseCode (p : FramePhase) : UInt64 :=
  match p with
  | .syncWait => 0
  | .lenByte => 1
  | .bodyStream => 2
  | .escaped => 3
  | .checksumByte => 4
  | .fault => 5
