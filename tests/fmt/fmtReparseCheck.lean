import Lean

/-!
Tests that the formatter keeps a command unformatted when the parser does not read the rendering of
the command with the structure that the formatter produced (`Lean.Fmt.checkReparse`). The inputs
that must stay unformatted have extra spaces, which a formatted rendering does not keep.
-/

open Lean Lean.Fmt

/-! Formatters that are wrong on purpose: -/

/-- `colGt` ends the numbers at the first one that does not start to the right of `nums`. -/
syntax (name := numsCmd) withPosition("nums" (colGt num)*) : command

elab_rules : command
  | `(nums $_*) => pure ()

/-- Puts each number at the start of a line of its own, which ends the command after `nums`. -/
@[fmt numsCmd]
def fmtNumsWrong : Fmt := fun stx => do
  let numDocs ← stx[1].getArgs.mapM fmt
  return numDocs.foldl (init := ← fmt stx[0]) fun doc numDoc => doc ++ hardNl ++ numDoc

nums  1  2

syntax (name := wrapTerm) "wrap " term:max : term

macro_rules
  | `(wrap $t) => `($t)

/-- Drops the parentheses around the argument of `wrap`. -/
@[fmt wrapTerm]
def fmtWrapWrong : Fmt := fun stx => do
  let arg := stx[1]
  let arg := if arg.isOfKind ``Parser.Term.paren then arg[1] else arg
  return (← fmt stx[0]) ++ space ++ (← fmt arg)

-- `wrap 1 + 2 * 3` parses as `(wrap 1) + (2 * 3)`, so `1 + 2` is not a unit anymore.
example : Nat := wrap  (1 + 2)  *  3

-- `wrap 1` keeps the structure of `wrap (1)`.
example : Nat := wrap  (1)

/-! A bug of a formatter of core that the check catches: -/

-- Without `;`, `cases` would take `, trivial` as a second target.
example (h : False) : False ∧ True :=
  ⟨by cases h;, trivial⟩
