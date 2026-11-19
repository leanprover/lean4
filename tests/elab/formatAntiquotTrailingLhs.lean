import Lean

/-!
# Formatting antiquotations on the left of trailing syntax

The formatter used to format the left operand of trailing syntax in a placeholder category instead
of the category of the trailing syntax, so it did not recognize antiquotations there.
-/

open Lean

elab "#format " s:str : command => Elab.Command.liftTermElabM do
  let stx ← ofExcept <| Parser.runParserCategory (← getEnv) `term s.getString
  logInfo m!"{← PrettyPrinter.ppCategory `term stx}"

/-- info: `($x + 2) -/
#guard_msgs in #format "`($x + 2)"

/-- info: `($x:term + 2) -/
#guard_msgs in #format "`($x:term + 2)"

/-- info: `($x + 2 + 3) -/
#guard_msgs in #format "`($x + 2 + 3)"

/-- info: `(tactic| $t <;> skip) -/
#guard_msgs in #format "`(tactic| $t <;> skip)"

/-! The quotation precheck prints quoted syntax in its error message. -/

syntax:65 term:65 " +++ " term:66 : term

def y := 1

/--
error: no macro or `[quot_precheck]` instance for syntax kind `«term_+++_»` found
  $x +++ y
This means we cannot eagerly check your notation/quotation for unbound identifiers; you can use `set_option quotPrecheck false` to disable this check.
-/
#guard_msgs in
example (x : Term) : MacroM Term := ``($x +++ y)
