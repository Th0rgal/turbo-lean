/- Tier C1 upstream-leg canary (roadmap leaf C1x, row R1): a scalar-subset
   program the frontend must lower end to end. The manifest leg runs it on
   every opt-in run; the leg is ok only when this file's outcome is
   lowered_llvm_emitted, so a frontend regression that rejects everything
   cannot read as 250 expected rejections. Manifest-external by design: it
   never counts toward clearing upstream_lean4_run_250_three_way.
   Proven live at the pin: emit-lnir rc 0, compile-llvm rc 0 (2026-11-26). -/
def c1xCanaryMix (x : UInt64) (y : UInt64) : UInt64 :=
  let s := x + (y <<< 3)
  let t := s ^^^ (x >>> 7)
  t &&& 0xFFFFFFFF

def c1xCanaryBranch (a : UInt32) (b : UInt32) : UInt32 :=
  if a < b then a + b else a - b
