import B2

/-! Export the exact artifacts covered by B2's active proof build and axiom audit. -/
def main (args : List String) : IO UInt32 := do
  let [outputStem] := args | do
    IO.eprintln "usage: lake env lean --run Emit.lean <output-prefix>"
    return 1
  let bytes := Backend.wordsBytes B2.Artifacts.fb.words
  IO.FS.writeBinFile (outputStem ++ ".bin") bytes
  IO.FS.writeFile (outputStem ++ ".s") B2.Artifacts.fa.text
  IO.println s!"wrote {bytes.size} bytes and assembly for {B2.Artifacts.fb.name}"
  return 0
