import Lean.Data.Lsp.Utf16

/-!
Tests that the column checkpoints `FileMap.ofString` records for long lines (#15646) do not change
the results of position conversions.
-/

open Lean

/-- `FileMap.toPosition` without checkpoints, counting from the start of the line. -/
partial def refToPosition (fmap : FileMap) (pos : String.Pos.Raw) : Position :=
  let str := fmap.source
  let ps := fmap.positions
  if ps.size >= 2 && pos <= ps.back! then
    let rec toColumn (i : String.Pos.Raw) (c : Nat) : Nat :=
      if i == pos || i.atEnd str then c
      else toColumn (i.next str) (c+1)
    let rec loop (b e : Nat) :=
      let posB := ps[b]!
      if e == b + 1 then { line := fmap.getLine b, column := toColumn posB 0 }
      else
        let m := (b + e) / 2;
        let posM := ps[m]!
        if pos == posM then { line := fmap.getLine m, column := 0 }
        else if pos > posM then loop m e
        else loop b m
    loop 0 (ps.size - 1)
  else if ps.isEmpty then
    ⟨0, 0⟩
  else
    ⟨fmap.getLastLine, ps.back!.byteDistance pos⟩

/-- `FileMap.leanPosToLspPos` without checkpoints, counting from the start of the line. -/
def refLeanPosToLspPos (fmap : FileMap) : Position → Lsp.Position
  | ⟨line, col⟩ => ⟨line - 1, String.codepointPosToUtf16PosFrom fmap.source col (fmap.lineStart line)⟩

/-- Compares the position conversions of `FileMap.ofString src` at every byte offset. -/
def check (src : String) : IO Unit := do
  let text := FileMap.ofString src
  -- Also covers offsets inside of code points and past the end of the file.
  for i in 0...(src.utf8ByteSize + 4) do
    let pos : String.Pos.Raw := ⟨i⟩
    let p := text.toPosition pos
    unless p == refToPosition text pos do
      throw <| .userError s!"toPosition {i}: {p} vs. {refToPosition text pos}"
    -- Also covers columns past the end of the line and the synthetic line 0.
    for p in [p, { p with column := p.column + 300 }, { p with line := 0 }] do
      unless text.leanPosToLspPos p == refLeanPosToLspPos text p do
        throw <| .userError s!"leanPosToLspPos {p}"
    unless text.utf8PosToLspPos pos == refLeanPosToLspPos text (refToPosition text pos) do
      throw <| .userError s!"utf8PosToLspPos {i}"

def longLine (n : Nat) : String :=
  String.join <| (List.range n).map fun i =>
    if i % 7 == 0 then "α" else if i % 11 == 0 then "𝔸" else if i % 13 == 0 then "∀" else "a"

#eval check ""
#eval check "abc\nαβγ\n\n𝔸𝔸\n"
#eval check (longLine 100)
#eval check (longLine 3000)
#eval check (longLine 3000 ++ "\n")
#eval check ("ab\n" ++ longLine 2000 ++ "\nαβ\n" ++ longLine 10 ++ "\n" ++ longLine 1500)
#eval check (String.join (List.replicate 1500 "𝔸"))
#eval check ("\n" ++ String.join (List.replicate 1500 "a") ++ "\n\n")
