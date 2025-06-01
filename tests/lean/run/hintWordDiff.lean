import Lean.Meta.Hint

/-! # Word-level diffs in hint suggestions

Word-level diffs in hint suggestions require careful display of whitespace, since it is frequently
impossible to both accurately render both deleted and inserted whitespace while also displaying a
snippet that recognizably maps to what will be inserted. These tests exercise the behavior of the
word-level diff generator to ensure that it is reasonable.
-/

open Lean Meta Hint

-- We reproduce this function here because it is private in `Lean.Meta.Hint`
private def mkDiffString (ds : Array (Diff.Action × String)) : String :=
  let rangeStrs := ds.map fun
    | (.insert, s) => String.mk (s.data.flatMap ([·, '\u0332'])) -- U+0332 Combining Low Line
    | (.delete, s) => String.mk (s.data.flatMap ([·, '\u0335'])) -- U+0335 Combining Short Stroke Overlay
    | (.skip  , s) => s
  rangeStrs.foldl (· ++ ·) ""

/-- info: "one two t̲h̲r̲e̲e̲" -/
#guard_msgs in
#eval readableDiff.wordDiff "one two" "one two three" |> mkDiffString

/-- info: "o̵n̵e̵a̲ two t̲h̲r̲e̲e̲" -/
#guard_msgs in
#eval readableDiff.wordDiff "one\ntwo" "a two three" |> mkDiffString

/-- info: "o̵n̵e̵a̲\ntwo t̲h̲r̲e̲e̲" -/
#guard_msgs in
#eval readableDiff.wordDiff "one two" "a\ntwo three" |> mkDiffString

/-- info: "one two" -/
#guard_msgs in
#eval readableDiff.wordDiff "one\ntwo" "one two" |> mkDiffString

/-- info: "one t̵w̵o̵ ̵three" -/
#guard_msgs in
#eval readableDiff.wordDiff "one two three" "one three" |> mkDiffString

/-- info: "a b" -/
#guard_msgs in
#eval readableDiff.wordDiff "a  b" "a b" |> mkDiffString

/-- info: "a ̵b̵" -/
#guard_msgs in
#eval readableDiff.wordDiff "a b" "a" |> mkDiffString

/-- info: "a̵b c" -/
#guard_msgs in
#eval readableDiff.wordDiff "a\nb c" "b c" |> mkDiffString

/--
info: "a l̵o̵n̵g̵e̵r̵l̲o̲n̲g̲\tstring w̵i̵t̵h̵ ̵ ̵ ̵w̵h̵i̵t̵e̵s̵p̵a̵c̵e̵in strange\n\np̵l̵a̵c̵e̵s̵\n̵a̵n̵d̵ ̵u̵n̵u̵s̵u̵a̵l̵spaces"
-/
#guard_msgs in
#eval readableDiff.wordDiff
  "a longer\nstring with   whitespace\n  in strange\nplaces and\n\nunusual\tspaces"
  "a long\tstring in strange\n\nspaces"
  |> mkDiffString

/--
info: def f (̵x̵ ̵:̵ ̵N̵a̵t̵)̵x̲ := x + 1
#check let c̵x̲ := 3̵1̵5̲ in
    f c̵x̲
-/
#guard_msgs in
#eval IO.println <| readableDiff.wordDiff
  "def f (x : Nat) := x + 1\n#check let c := 31 in\n  f c"
  "def f x := x + 1\n#check let x := 5 in\n    f x"
  |> mkDiffString
