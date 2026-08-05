import Lean

/-! # Pretty-printing indented `tacticSeq` arguments

A multi-tactic indented `tacticSeq` breaks onto its own rows via a forced `align`. If the
`ppSpace` separator before it flattens instead of breaking, the flattened space is stranded at
the end of the row; if the `align` breaks after the separator already did, it leaves a
whitespace-only blank line.
-/

open Lean PrettyPrinter

/-- Pretty-print tactic source at the given width. -/
def ppTactic (src : String) (width : Nat := 100) : CoreM String := do
  match Parser.runParserCategory (← getEnv) `tactic src "<test>" with
  | .error e => throwError e
  | .ok stx => return (← ppCategory `tactic stx).pretty width

/--
info: iterate 1
  skip
  skip
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "iterate 1\n  skip\n  skip")

-- at narrow widths the separator breaks first, and the `align` must not add a blank line
/--
info: iterate 1
  skip
  skip
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "iterate 1\n  skip\n  skip" (width := 12))

-- the same rules hold for user-defined `ppSpace tacticSeq` syntax, not just core `iterate`
syntax "myiter" num ppSpace tacticSeq : tactic

/--
info: myiter 1
  skip
  skip
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "myiter 1\n  skip\n  skip")

-- a single-tactic argument stays flat
/--
info: iterate 1 skip
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "iterate 1 skip")

-- a `tacticSeq` after a keyword with no `ppSpace` still breaks onto its own rows
/--
info: all_goals
  skip
  skip
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "all_goals\n  skip\n  skip")

-- semicolon-separated sequences stay on one row
/--
info: iterate 1 (skip; skip)
-/
#guard_msgs (whitespace := exact) in
#eval show CoreM Unit from do
  IO.println (← ppTactic "iterate 1 (skip; skip)")

-- pretty-printed output must re-parse and re-format to itself
/--
info: true
-/
#guard_msgs in
#eval show CoreM Unit from do
  let once ← ppTactic "iterate 1\n  skip\n  skip"
  IO.println ((← ppTactic once) == once)
