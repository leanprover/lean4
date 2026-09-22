/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

import ParseNumberCheck.Decimal

/-!
Checks the `OfScientific Float` and `OfScientific Float32` instances — the
decimal-to-float conversion behind floating-point literals — against test vectors
in the [`parse-number-fxx-test-data`](https://github.com/nigeltao/parse-number-fxx-test-data)
format. Each non-blank, non-comment line of such a file has four space-separated
fields:

  <binary16-hex> <binary32-hex> <binary64-hex> <decimal-string>

The first three fields are the correctly rounded (round-to-nearest, ties-to-even)
`binary16`, `binary32`, and `binary64` bit patterns of the decimal value in the
fourth field, as 4, 8, and 16 hexadecimal digits respectively. This harness parses
the decimal string, feeds it through `OfScientific.ofScientific` for `Float` and
`Float32` exactly as the elaborator does for a literal, and compares the resulting
bit patterns against the `binary64` and `binary32` fields. The `binary16` field is
ignored (Lean has no `binary16` type). Results are compared bit-for-bit; decimal
parsing never yields a `NaN`, so no `NaN`-class comparison is needed.

  lake exe parse-number-check [DIR] [--all]

With a directory argument, every `*.txt` file under `DIR` (recursively) is checked;
point it at the `data/` directory of a full `parse-number-fxx-test-data` checkout,
which is far too large to vendor here. With no directory argument it falls back to
the tiny `test-data/` directory committed alongside this test, which exercises a
handful of basic cases and confirms the vector parser itself works. By default only
the first 20 failures are shown; pass `--all` to show them all.
-/

/-- The committed fallback vectors, used when no directory is given on the command line. -/
def defaultDataDir : System.FilePath := "test-data"

/-- The number of failures shown before the rest are suppressed unless `--all` is given. -/
def defaultMaxShown : Nat := 20

/-- Parse a hexadecimal string into a `UInt64`, or `none` if it contains a non-hex digit. -/
def hexToUInt64? (s : String) : Option UInt64 :=
  if s.isEmpty then none
  else s.foldl (init := some 0) fun acc c => do
    let acc ← acc
    let d ←
      if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    some (acc * 16 + UInt64.ofNat d)

/-- Render `x` as a zero-padded hexadecimal string of `width` digits. -/
def toHexWidth (width : Nat) (x : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 x)
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- All `*.txt` files under `dir`, recursively. -/
partial def txtFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      out := out ++ (← txtFiles entry.path)
    else if entry.path.toString.endsWith ".txt" then
      out := out.push entry.path
  return out

/--
A single parsed vector line: the decimal string and the expected `binary32`/`binary64`
bit patterns. The original line is kept for diagnostics.
-/
structure Sample where
  decimal : Decimal
  source : String
  expected32 : UInt32
  expected64 : UInt64

/--
Parse the lines of a vector file into `Sample`s. Blank lines and `#` comments are
skipped; malformed lines (wrong field count, bad hex, or a decimal string the
parser rejects) are reported to stderr under `label` and counted as failures so a
broken vector or parser surfaces rather than being silently dropped.
-/
def parseSamples (label : String) (lines : Array String) :
    IO (Array Sample × Nat) := do
  let mut samples := #[]
  let mut malformed := 0
  for line in lines do
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty || trimmed.startsWith "#" then
      continue
    let tokens := trimmed.split " " |>.filter (!·.isEmpty) |>.toStringList
    match tokens with
    | [_f16, f32, f64, str] =>
      match hexToUInt64? f32, hexToUInt64? f64, parseDecimal str with
      | some e32, some e64, some decimal =>
        samples := samples.push {
          decimal, source := str, expected32 := e32.toUInt32, expected64 := e64
        }
      | _, _, _ =>
        malformed := malformed + 1
        IO.eprintln s!"malformed line in {label}: {trimmed}"
    | _ =>
      malformed := malformed + 1
      IO.eprintln s!"malformed line in {label}: {trimmed}"
  return (samples, malformed)

public def main (args : List String) : IO UInt32 := do
  let (flags, positional) := args.partition (·.startsWith "--")
  let maxShown := if flags.contains "--all" then 1000000000 else defaultMaxShown

  let dataDir : System.FilePath :=
    match positional with
    | dir :: _ => dir
    | [] => defaultDataDir
  unless (← dataDir.pathExists) do
    IO.eprintln s!"error: data directory '{dataDir}' does not exist"
    return 2
  unless (← dataDir.isDir) do
    IO.eprintln s!"error: '{dataDir}' is not a directory"
    return 2

  let files := (← txtFiles dataDir).qsort (·.toString < ·.toString)
  if files.isEmpty then
    IO.eprintln s!"error: no *.txt vector files found under '{dataDir}'"
    return 2

  let mut grandTotal := 0
  let mut grandFailures := 0
  let mut shown := 0
  for path in files do
    let label := path.toString
    let (samples, malformed) ← parseSamples label (← IO.FS.lines path)

    let mut fails := 0
    for s in samples do
      let actual64 := s.decimal.toFloat.toBits
      let actual32 := s.decimal.toFloat32.toBits
      let ok64 := actual64 == s.expected64
      let ok32 := actual32 == s.expected32
      unless ok64 && ok32 do
        fails := fails + 1
        if shown < maxShown then
          shown := shown + 1
          unless ok64 do
            IO.eprintln s!"FAIL [{label}] Float: \"{s.source}\" = \
              {toHexWidth 16 s.expected64.toNat}, got {toHexWidth 16 actual64.toNat}"
          unless ok32 do
            IO.eprintln s!"FAIL [{label}] Float32: \"{s.source}\" = \
              {toHexWidth 8 s.expected32.toNat}, got {toHexWidth 8 actual32.toNat}"

    let total := samples.size + malformed
    IO.println s!"{label}: {total} vectors, {fails + malformed} failures"
    grandTotal := grandTotal + total
    grandFailures := grandFailures + fails + malformed

  if grandFailures > shown then
    IO.eprintln s!"... ({grandFailures - shown} further failures suppressed; pass --all to show them)"
  IO.println s!"total: {grandTotal} vectors, {grandFailures} failures across {files.size} file(s)"
  return if grandFailures == 0 then 0 else 1
