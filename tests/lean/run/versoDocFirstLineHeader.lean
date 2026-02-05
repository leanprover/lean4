import Lean
set_option doc.verso true

open Lean Elab Term in
def printLastModDoc : TermElabM Unit := do
  let docs := getMainVersoModuleDocs (← getEnv)
  let last? := docs.snippets.toArray.back?
  let depth := docs.terminalNesting
  match last? with
  | none => IO.println "No mod docs"
  | some d => IO.println s!"Nesting: {depth}"; IO.println (repr d)

-- First-line header in module doc
/-! # Header (w/ space)-/

/--
info: Nesting: (some 0)
{ text := #[],
  sections := #[(0,
                 { pos := { line := 14, column := 4 },
                   charUtf16 := 4,
                   endPos := { line := 14, column := 23 },
                   endCharUtf16 := 23 },
                 { title := #[Lean.Doc.Inline.text "Header (w/ space)"],
                   titleString := "Header \\(w/ space\\)",
                   metadata := none,
                   content := #[],
                   subParts := #[] })],
  declarationRange := { pos := { line := 14, column := 0 },
                        charUtf16 := 0,
                        endPos := { line := 14, column := 25 },
                        endCharUtf16 := 25 } }
-/
#guard_msgs in
#eval printLastModDoc

-- First-line header followed by nested headers in module doc
/-! # Level 1

## Level 2
-/

/--
info: Nesting: (some 1)
{ text := #[],
  sections := #[(0,
                 { pos := { line := 38, column := 4 },
                   charUtf16 := 4,
                   endPos := { line := 38, column := 13 },
                   endCharUtf16 := 13 },
                 { title := #[Lean.Doc.Inline.text "Level 1"],
                   titleString := "Level 1",
                   metadata := none,
                   content := #[],
                   subParts := #[] }),
                (1,
                 { pos := { line := 40, column := 0 },
                   charUtf16 := 0,
                   endPos := { line := 40, column := 10 },
                   endCharUtf16 := 10 },
                 { title := #[Lean.Doc.Inline.text "Level 2"],
                   titleString := "Level 2",
                   metadata := none,
                   content := #[],
                   subParts := #[] })],
  declarationRange := { pos := { line := 38, column := 0 },
                        charUtf16 := 0,
                        endPos := { line := 41, column := 2 },
                        endCharUtf16 := 2 } }
-/
#guard_msgs in
#eval printLastModDoc


-- First-line header in declaration doc
/-- # Header
-/
def foo := 1

-- First-line header followed by nested headers in declaration doc
/-- # Level 1

## Level 2
-/
def bar := 1

-- No space after /-!
/-!# Header (no space)
-/

/--
info: Nesting: (some 0)
{ text := #[],
  sections := #[(0,
                 { pos := { line := 88, column := 3 },
                   charUtf16 := 3,
                   endPos := { line := 88, column := 22 },
                   endCharUtf16 := 22 },
                 { title := #[Lean.Doc.Inline.text "Header (no space)"],
                   titleString := "Header \\(no space\\)",
                   metadata := none,
                   content := #[],
                   subParts := #[] })],
  declarationRange := { pos := { line := 88, column := 0 },
                        charUtf16 := 0,
                        endPos := { line := 89, column := 2 },
                        endCharUtf16 := 2 } }
-/
#guard_msgs in
#eval printLastModDoc


-- First-line header with deeper nesting
/-! # First line header

## Second level

### Third level
-/

-- Error: header nesting violation with first-line header
/-- error: Incorrect header nesting: expected at most `##` but got `####` -/
#guard_msgs in
/-! # A
#### D
-/

/-- error: Incorrect header nesting: expected at most `####` but got `#####` -/
#guard_msgs in
/-! # Level 1

## Level 2

### Level 3

##### Level 5
-/

-- Cross-snippet nesting with first-line header
/-! # Top -/
/-! ## Sub -/
/-! ### SubSub -/
