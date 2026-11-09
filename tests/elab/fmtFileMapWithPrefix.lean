import Lean

/-!
Tests `Lean.Fmt.fileMapWithPrefix`, which computes the `FileMap` of a prefix followed by the rest of
a file from the `FileMap` of the file, against `FileMap.ofString` of the same text.
-/

open Lean Lean.Fmt

/-- Checks `fileMapWithPrefix` for each valid position of `source`. -/
def check (source pre : String) : Bool := Id.run do
  let text := FileMap.ofString source
  for i in [0:source.utf8ByteSize + 1] do
    let some pos := text.source.pos? ⟨i⟩
      | continue
    let expected := FileMap.ofString (pre ++ text.source.extract pos text.source.endPos)
    let actual := fileMapWithPrefix text pre pos
    if actual.source != expected.source || actual.positions != expected.positions then
      return false
  return true

#guard ["", "a", "\n", "a\n", "ab\ncd", "ab\ncd\n", "\n\nα\nβγ\n\n", "α\nβ"].all fun source =>
  ["", "x", "\n", "x\n", "xy\nz", "α\n\n"].all fun pre => check source pre
