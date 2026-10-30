import Lean.Data.Markdown.Unicode.CharacterClasses

/-!
Checks `isUnicodeWhitespace` and `isUnicodePunctuation` against Unicode's `DerivedGeneralCategory.txt`,
included in `unicode/DerivedGeneralCategory.txt` together with its license. Whitespace must be
exactly the `Zs` category plus tab, line feed, form feed, and carriage return, and punctuation must be
exactly the `P` and `S` categories. Every character of those categories is checked; for the other
ranges of the file, the ends and the middle of each range are checked.
-/

open Lean Markdown

/-- The value of a hexadecimal numeral. -/
def hex? (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.foldl (init := some 0) fun acc c => do
    let n ← acc
    guard c.isHexDigit
    let d := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    return n * 16 + d

/-- The ranges of `DerivedGeneralCategory.txt` with their general category. -/
def readCategories (path : System.FilePath) : IO (Array (Nat × Nat × String)) := do
  let mut out := #[]
  for line in (← IO.FS.lines path) do
    let line := (line.splitOn "#")[0]!.trimAscii.toString
    if line.isEmpty then continue
    let [range, cat] := line.splitOn ";" |>.map (·.trimAscii.toString)
      | throw <| .userError s!"unexpected line: {line}"
    let (lo, hi) ← match range.splitOn ".." |>.map hex? with
      | [some n] => pure (n, n)
      | [some lo, some hi] => pure (lo, hi)
      | _ => throw <| .userError s!"bad range: {range}"
    out := out.push (lo, hi, cat)
  return out

/-- Whether `cat` is a punctuation or symbol category. -/
def isPS (cat : String) : Bool := cat.startsWith "P" || cat.startsWith "S"

/--
The code points of a range to check: every one when `every` is set, otherwise its ends and its
middle. Surrogates are not characters and are left out.
-/
def points (lo hi : Nat) (every : Bool) : List Nat :=
  let ps := if every then (List.range (hi - lo + 1)).map (lo + ·) else [lo, (lo + hi) / 2, hi]
  ps.filter fun n => !(0xD800 ≤ n && n ≤ 0xDFFF)

/--
Code points that `isUnicodePunctuation` classifies differently from the file. Every punctuation or
symbol character is checked, as is every character of the other ranges up to 1024 code points long;
the longer ranges, which are unassigned planes and the large letter and syllable blocks, are checked
at their ends and middle.
-/
def punctuationMismatches (table : Array (Nat × Nat × String)) : List Nat := Id.run do
  let mut out := []
  for (lo, hi, cat) in table do
    for n in points lo hi (isPS cat || hi - lo < 1024) do
      if isUnicodePunctuation (Char.ofNat n) != isPS cat then out := n :: out
  return out.reverse

/-- Code points that `isUnicodeWhitespace` classifies differently from the file. -/
def whitespaceMismatches (table : Array (Nat × Nat × String)) : List Nat := Id.run do
  let mut out := []
  for (lo, hi, cat) in table do
    for n in points lo hi (cat == "Zs" || hi < 0x3100) do
      let want := cat == "Zs" || n == 0x9 || n == 0xA || n == 0xC || n == 0xD
      if isUnicodeWhitespace (Char.ofNat n) != want then out := n :: out
  return out.reverse

-- The file's version, so that the classification is pinned.
/-- info: some "# DerivedGeneralCategory-18.0.0.txt" -/
#guard_msgs in #eval do
  return (← IO.FS.lines "unicode/DerivedGeneralCategory.txt").find? fun (l : String) =>
    l.startsWith "# Derived"

-- The number of `Zs` characters and of punctuation and symbol characters, as a check that the file
-- was read.
/-- info: (17, 9620) -/
#guard_msgs in #eval do
  let table ← readCategories "unicode/DerivedGeneralCategory.txt"
  let zs : Nat := table.foldl (init := 0) fun n (lo, hi, cat) => if cat == "Zs" then n + hi - lo + 1 else n
  let ps : Nat := table.foldl (init := 0) fun n (lo, hi, cat) => if isPS cat then n + hi - lo + 1 else n
  return (zs, ps)

/-- info: [] -/
#guard_msgs in #eval do return punctuationMismatches (← readCategories "unicode/DerivedGeneralCategory.txt")

/-- info: [] -/
#guard_msgs in #eval do return whitespaceMismatches (← readCategories "unicode/DerivedGeneralCategory.txt")
