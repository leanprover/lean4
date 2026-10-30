import Lean.Data.Markdown.Unicode.CaseFolding
import Std.Data.HashMap

/-!
Checks `caseFold` against Unicode's `CaseFolding.txt`, included in `unicode/CaseFolding.txt`
together with its license. The covered set is the Latin-1 Supplement and Greek and Coptic blocks
together with every character whose folding, by the file's entries with status `C` and `F`, consists
of ASCII, Latin-1, or Greek and Coptic characters. Every code point in the covered set must fold as
the file says, or to itself when it has no entry, and every entry outside the covered set must fold
to itself.
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

/-- The full case foldings (statuses `C` and `F`) of `CaseFolding.txt`, by code point. -/
def readFoldings (path : System.FilePath) : IO (Std.HashMap Nat (List Nat)) := do
  let mut table := {}
  for line in (← IO.FS.lines path) do
    let line := (line.splitOn "#")[0]!.trimAscii.toString
    if line.isEmpty then continue
    let [code, status, mapping, _] := line.splitOn ";" |>.map (·.trimAscii.toString)
      | throw <| .userError s!"unexpected line: {line}"
    if status == "C" || status == "F" then
      let some n := hex? code | throw <| .userError s!"bad code point: {code}"
      table := table.insert n ((mapping.splitOn " ").filterMap hex?)
  return table

/-- Whether code point `n` is in one of the covered blocks, or is ASCII. -/
def inBlocks (n : Nat) : Bool := n < 0x100 || (0x370 ≤ n && n ≤ 0x3FF)

/-- Whether code point `n` is covered: in the blocks, or folding entirely into them. -/
def covered (table : Std.HashMap Nat (List Nat)) (n : Nat) : Bool :=
  inBlocks n || (table[n]?.any (·.all inBlocks))

/-- The folding of `n` that the file requires of a covered character. -/
def expected (table : Std.HashMap Nat (List Nat)) (n : Nat) : String :=
  String.mk ((table[n]?.getD [n]).map Char.ofNat)

/--
The code points whose folding is wrong, with the expected and actual foldings: covered code points
that differ from the file, and entries outside the covered set that do not fold to themselves.
-/
def mismatches (table : Std.HashMap Nat (List Nat)) : List (Nat × String × String) := Id.run do
  let mut out := []
  let check (n : Nat) (want : String) : Option (Nat × String × String) :=
    let got := caseFold (Char.ofNat n)
    if got == want then none else some (n, want, got)
  for n in List.range 0x100 ++ (List.range 0x90).map (0x370 + ·) do
    if let some m := check n (expected table n) then out := m :: out
  for (n, _) in table.toList do
    if !inBlocks n then
      let want := if covered table n then expected table n else String.singleton (Char.ofNat n)
      if let some m := check n want then out := m :: out
  return out.reverse

-- The file's version, so that the covered folding is pinned.
/-- info: "# CaseFolding-18.0.0.txt" -/
#guard_msgs in #eval do return (← IO.FS.lines "unicode/CaseFolding.txt")[0]!

-- The number of entries in the file and in the covered set, as a check that the file was read.
/-- info: (1606, 150) -/
#guard_msgs in #eval do
  let table ← readFoldings "unicode/CaseFolding.txt"
  let coveredEntries : Nat := table.toList.countP fun (p : Nat × List Nat) => covered table p.1
  return (table.size, coveredEntries)

/-- info: [] -/
#guard_msgs in #eval do return mismatches (← readFoldings "unicode/CaseFolding.txt")
