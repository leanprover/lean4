/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

import TestFloatCheck.CheckUtil
import Std.Time

/-!
Checks the `binary32` and `binary64` operations against the test vectors
committed under `test-vectors/`. Each file is run against two backends: the
`model` (`Float.Model`/`Float32.Model`) and `native`, Lean's built-in `Float`
and `Float32` operations (the hardware the model models, included as a sanity
check on the harness and vectors). Running

  lake exe testfloat-check

with no arguments discovers every `*.txt.gz` vector file under `test-vectors/`,
decompresses it (by shelling out to `gzip -dc`), and checks it; an optional list
of substring filters restricts the run to matching files, e.g.

  lake exe testfloat-check f64_mul       -- only files whose label contains "f64_mul"

The vector files are in Berkeley TestFloat format: each line is
`<operand1> [<operand2>] <expected> <flags>` (the second operand is absent for
unary operations) with all fields in hexadecimal and floats given as their bit
patterns — 16 digits for `binary64`, 8 for `binary32`. The exception-flags field
is ignored since the model does not compute flags. NaN results are compared as a
class, not bit-for-bit, since the model produces a canonical NaN rather than
propagating payloads.

The committed vectors come from three suites (one subdirectory each); see
`test-vectors/README.md` for how they are produced. By default only the first 20
failures are shown; pass `--all` to show them all.

Each file is decompressed and its lines parsed into operand/expected bit patterns
exactly once; the per-backend wall-clock time printed alongside each result
(measured with `Std.Time.Timestamp`/`Duration`) therefore covers only the
operations themselves, letting the model be compared against the native hardware.
-/

open Float.Model
open Std.Time (Timestamp Duration)

/-- The directory holding the committed test-vector files, relative to the repo root. -/
def vectorsDir : System.FilePath := "test-vectors"

/--
A named set of implementations, keyed by the `<precision>_<operation>` basename
of a vector file (e.g. `f64_add`, `f32_sqrt`). A binary operation is checked
against lines of the form `<a> <b> <expected> <flags>`, a unary operation
against lines of the form `<a> <expected> <flags>`.
-/
structure Backend where
  /-- Short name shown in the output, e.g. `model` or `native`. -/
  name : String
  /-- The implementations this backend provides, keyed by vector-file basename. -/
  operations : List (String × Check)

/-- The `Float.Model`/`Float32.Model` implementations. -/
def modelBackend : Backend where
  name := "model"
  operations :=
    [("f64_add", f64Check (.binary '+' (modelBinop Float.Model.add))),
     ("f64_sub", f64Check (.binary '-' (modelBinop Float.Model.sub))),
     ("f64_mul", f64Check (.binary '*' (modelBinop Float.Model.mul))),
     ("f64_div", f64Check (.binary '/' (modelBinop Float.Model.div))),
     ("f64_sqrt", f64Check (.unary "sqrt" (modelUnop Float.Model.sqrt))),
     ("f64_eq", f64Check (.binary '=' (modelCompare Float.Model.beq))),
     ("f64_le", f64Check (.binary '≤' (modelCompare Float.Model.le))),
     ("f64_lt", f64Check (.binary '<' (modelCompare Float.Model.lt))),
     ("f32_add", f32Check (.binary '+' (modelBinop32 Float32.Model.add))),
     ("f32_sub", f32Check (.binary '-' (modelBinop32 Float32.Model.sub))),
     ("f32_mul", f32Check (.binary '*' (modelBinop32 Float32.Model.mul))),
     ("f32_div", f32Check (.binary '/' (modelBinop32 Float32.Model.div))),
     ("f32_sqrt", f32Check (.unary "sqrt" (modelUnop32 Float32.Model.sqrt))),
     ("f32_eq", f32Check (.binary '=' (modelCompare32 Float32.Model.beq))),
     ("f32_le", f32Check (.binary '≤' (modelCompare32 Float32.Model.le))),
     ("f32_lt", f32Check (.binary '<' (modelCompare32 Float32.Model.lt))),
     ("ui32_to_f64", f64Check (.unary "ui32_to_f64" modelOfUInt32)),
     ("ui64_to_f64", f64Check (.unary "ui64_to_f64" modelOfUInt64)),
     ("i32_to_f64", f64Check (.unary "i32_to_f64" modelOfInt32)),
     ("i64_to_f64", f64Check (.unary "i64_to_f64" modelOfInt64)),
     ("ui32_to_f32", f32Check (.unary "ui32_to_f32" modelOfUInt32_32)),
     ("ui64_to_f32", f32Check (.unary "ui64_to_f32" modelOfUInt64_32)),
     ("i32_to_f32", f32Check (.unary "i32_to_f32" modelOfInt32_32)),
     ("i64_to_f32", f32Check (.unary "i64_to_f32" modelOfInt64_32)),
     ("f64_to_ui32", i32Check (.unary "f64_to_ui32" modelToUInt32)),
     ("f64_to_ui64", i64Check (.unary "f64_to_ui64" modelToUInt64)),
     ("f64_to_i32", i32Check (.unary "f64_to_i32" modelToInt32)),
     ("f64_to_i64", i64Check (.unary "f64_to_i64" modelToInt64)),
     ("f32_to_ui32", i32Check (.unary "f32_to_ui32" modelToUInt32_32)),
     ("f32_to_ui64", i64Check (.unary "f32_to_ui64" modelToUInt64_32)),
     ("f32_to_i32", i32Check (.unary "f32_to_i32" modelToInt32_32)),
     ("f32_to_i64", i64Check (.unary "f32_to_i64" modelToInt64_32))]

/-- Lean's native `Float`/`Float32` implementations (the hardware the model models). -/
def nativeBackend : Backend where
  name := "native"
  operations :=
    [("f64_add", f64Check (.binary '+' (nativeBinop Float.add))),
     ("f64_sub", f64Check (.binary '-' (nativeBinop Float.sub))),
     ("f64_mul", f64Check (.binary '*' (nativeBinop Float.mul))),
     ("f64_div", f64Check (.binary '/' (nativeBinop Float.div))),
     ("f64_sqrt", f64Check (.unary "sqrt" (nativeUnop Float.sqrt))),
     ("f64_eq", f64Check (.binary '=' (nativeCompare Float.beq))),
     ("f64_le", f64Check (.binary '≤' (nativeCompare (fun a b => decide (a ≤ b))))),
     ("f64_lt", f64Check (.binary '<' (nativeCompare (fun a b => decide (a < b))))),
     ("f32_add", f32Check (.binary '+' (nativeBinop32 Float32.add))),
     ("f32_sub", f32Check (.binary '-' (nativeBinop32 Float32.sub))),
     ("f32_mul", f32Check (.binary '*' (nativeBinop32 Float32.mul))),
     ("f32_div", f32Check (.binary '/' (nativeBinop32 Float32.div))),
     ("f32_sqrt", f32Check (.unary "sqrt" (nativeUnop32 Float32.sqrt))),
     ("f32_eq", f32Check (.binary '=' (nativeCompare32 Float32.beq))),
     ("f32_le", f32Check (.binary '≤' (nativeCompare32 (fun a b => decide (a ≤ b))))),
     ("f32_lt", f32Check (.binary '<' (nativeCompare32 (fun a b => decide (a < b))))),
     ("ui32_to_f64", f64Check (.unary "ui32_to_f64" nativeOfUInt32)),
     ("ui64_to_f64", f64Check (.unary "ui64_to_f64" nativeOfUInt64)),
     ("i32_to_f64", f64Check (.unary "i32_to_f64" nativeOfInt32)),
     ("i64_to_f64", f64Check (.unary "i64_to_f64" nativeOfInt64)),
     ("ui32_to_f32", f32Check (.unary "ui32_to_f32" nativeOfUInt32_32)),
     ("ui64_to_f32", f32Check (.unary "ui64_to_f32" nativeOfUInt64_32)),
     ("i32_to_f32", f32Check (.unary "i32_to_f32" nativeOfInt32_32)),
     ("i64_to_f32", f32Check (.unary "i64_to_f32" nativeOfInt64_32)),
     ("f64_to_ui32", i32Check (.unary "f64_to_ui32" nativeToUInt32)),
     ("f64_to_ui64", i64Check (.unary "f64_to_ui64" nativeToUInt64)),
     ("f64_to_i32", i32Check (.unary "f64_to_i32" nativeToInt32)),
     ("f64_to_i64", i64Check (.unary "f64_to_i64" nativeToInt64)),
     ("f32_to_ui32", i32Check (.unary "f32_to_ui32" nativeToUInt32_32)),
     ("f32_to_ui64", i64Check (.unary "f32_to_ui64" nativeToUInt64_32)),
     ("f32_to_i32", i32Check (.unary "f32_to_i32" nativeToInt32_32)),
     ("f32_to_i64", i64Check (.unary "f32_to_i64" nativeToInt64_32))]

/-- The backends each vector file is checked against. -/
def backends : List Backend := [modelBackend, nativeBackend]

/-- All `*.txt.gz` vector files under `dir`, recursively. -/
partial def gzVectorFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in (← dir.readDir) do
    if ← entry.path.isDir then
      out := out ++ (← gzVectorFiles entry.path)
    else if entry.path.toString.endsWith ".txt.gz" then
      out := out.push entry.path
  return out

/-- The `<precision>_<operation>` key of a `*.txt.gz` vector file, e.g. `f64_add`. -/
def vectorKey (path : System.FilePath) : Option String := do
  let name ← path.fileName
  guard (name.endsWith ".txt.gz")
  return (name.dropEnd ".txt.gz".length).toString

/-- Whether `s` contains `sub` as a substring (used for the command-line filters). -/
def containsSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The number of failures shown before the rest are suppressed unless `--all` is given. -/
def defaultMaxShown : Nat := 20

/--
A single parsed vector line: the operand bit pattern(s) and the expected result.
The second operand `b` is unused for unary operations.
-/
structure Sample where
  a : UInt64
  b : UInt64
  expected : UInt64

/--
Parse the decompressed `lines` of a vector file into `Sample`s, doing the hex
decoding once per file rather than once per backend. `arityCheck` is consulted
only to decide whether each line carries one operand or two — every backend that
checks a given file agrees on its arity. Malformed lines are reported to stderr
under `label` and skipped. Factoring this out keeps the per-backend timing in
`main` measuring only the operations, not the parsing.
-/
def parseSamples (arityCheck : Check) (label : String) (lines : Array String) :
    IO (Array Sample) := do
  let mut samples := #[]
  for line in lines do
    let tokens := line.trimAscii.toString.split " " |>.filter (!·.isEmpty) |>.toStringList
    unless tokens.isEmpty do
      let parsed : Option Sample :=
        match arityCheck.op, tokens.mapM hexToUInt64? with
        | .binary _ _, some (a :: b :: expected :: _) => some { a, b, expected }
        | .unary _ _, some (a :: expected :: _) => some { a, b := 0, expected }
        | _, _ => none
      match parsed with
      | none => IO.eprintln s!"malformed line in {label}: {line.trimAscii.toString}"
      | some s => samples := samples.push s
  return samples

public def main (args : List String) : IO UInt32 := do
  let (flags, filters) := args.partition (·.startsWith "--")
  let maxShown := if flags.contains "--all" then 1000000000 else defaultMaxShown

  unless (← vectorsDir.pathExists) do
    IO.eprintln s!"error: vector directory {vectorsDir} not found (run from the repository root)"
    return 2
  let files := (← gzVectorFiles vectorsDir).qsort (·.toString < ·.toString)
  if files.isEmpty then
    IO.eprintln s!"error: no *.txt.gz vector files found under {vectorsDir}"
    return 2

  let mut grandTotal := 0
  let mut grandFailures := 0
  let mut shown := 0
  let mut ran := 0
  -- Accumulated computation time per backend, aligned positionally with `backends`.
  let mut grandDurations : Array Duration := .replicate backends.length 0
  for path in files do
    let some key := vectorKey path
      | IO.eprintln s!"skipping {path}: not a recognizable vector file"; continue
    let suite := (path.parent.bind (·.fileName)).getD "?"
    let label := s!"{suite}/{key}"
    if !filters.isEmpty && !filters.any (containsSubstr label ·) then
      continue
    unless backends.all (·.operations.any (·.1 == key)) do
      IO.eprintln s!"error: {path} names unknown operation '{key}'"; return 2

    -- Decompress the vector file once by streaming `gzip -dc <path>`, then check
    -- the materialized lines against every backend.
    let child ← IO.Process.spawn
      { cmd := "gzip", args := #["-dc", path.toString], stdout := .piped }
    let stdout := child.stdout
    let mut lines := #[]
    let mut done := false
    while !done do
      let line ← stdout.getLine
      if line.isEmpty then
        done := true
      else
        lines := lines.push line
    let exit ← child.wait
    if exit != 0 then
      IO.eprintln s!"error: gzip -dc {path} exited with status {exit}"
      return 2

    -- Parse the decompressed lines once, before checking any backend, so the
    -- timing below covers only the operations and not the hex parsing. Every
    -- backend that checks this file agrees on the operation's arity, so the
    -- `modelBackend` entry suffices to drive the parse.
    let some (_, arityCheck) := modelBackend.operations.find? (·.1 == key)
      | IO.eprintln s!"error: {path} names unknown operation '{key}'"; return 2
    let samples ← parseSamples arityCheck label lines

    for (backend, i) in backends.zipIdx do
      let some (_, check) := backend.operations.find? (·.1 == key)
        | continue
      let blabel := s!"{label} [{backend.name}]"
      -- Time only the computation: run every operation, collecting the failing
      -- samples, and keep all I/O and hex rendering out of the timed region.
      let start ← Timestamp.now
      let mut fails := #[]
      for s in samples do
        let actual := match check.op with
          | .binary _ op => op s.a s.b
          | .unary _ op => op s.a
        let ok := actual == s.expected || (check.isNaN actual && check.isNaN s.expected)
        unless ok do
          fails := fails.push (s, actual)
      let elapsed ← Timestamp.since start

      for (s, actual) in fails do
        if shown < maxShown then
          shown := shown + 1
          let description := match check.op with
            | .binary symbol _ => s!"{check.toHex s.a} {symbol} {check.toHex s.b}"
            | .unary name _ => s!"{name}({check.toHex s.a})"
          IO.eprintln
            s!"FAIL [{blabel}]: {description} = {check.toHex s.expected}, \
               {backend.name} returned {check.toHex actual}"
      IO.println s!"{blabel}: {samples.size} tests, {fails.size} failures ({elapsed})"
      grandTotal := grandTotal + samples.size
      grandFailures := grandFailures + fails.size
      grandDurations := grandDurations.modify i (· + elapsed)
    ran := ran + 1

  if grandFailures > shown then
    IO.eprintln s!"... ({grandFailures - shown} further failures suppressed; pass --all to show them)"
  IO.println s!"total: {grandTotal} tests, {grandFailures} failures across {ran} file(s)"
  for (backend, i) in backends.zipIdx do
    IO.println s!"total time [{backend.name}]: {grandDurations[i]!}"
  return if grandFailures == 0 then 0 else 1
