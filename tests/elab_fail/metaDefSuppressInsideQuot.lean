import Lean

/-!
Tests that the `meta` declaration modifier applies the parser context flag
`suppressInsideQuot` to the declaration body, matching the unconditional behavior of
`macro`/`macro_rules`/`elab`/`elab_rules`.

We define a custom term parser that emits a parser error whenever it is invoked inside
a quotation with `suppressInsideQuot = false`. The parser succeeds inside `meta def` and
`macro` bodies and fails inside a regular `def` body.
-/

open Lean Parser PrettyPrinter

private def suppressGuardFn : ParserFn := fun c s =>
  if c.quotDepth > 0 && !c.suppressInsideQuot then
    s.mkUnexpectedError "suppressInsideQuot is not set"
  else
    s

private def suppressGuard : Parser :=
  { fn := suppressGuardFn, info := epsilonInfo }

@[combinator_formatter suppressGuard] def suppressGuard.formatter : Formatter := pure ()
@[combinator_parenthesizer suppressGuard] def suppressGuard.parenthesizer : Parenthesizer := pure ()

@[term_parser]
private def suppressMarker : Parser :=
  leading_parser "%%check_suppress%%" >> suppressGuard

-- `meta def` body: our parser combinator sets `suppressInsideQuot`, so the guard passes.
private meta def metaTest : MacroM Syntax := `(%%check_suppress%%)

-- `macro` body: built-in `suppressInsideQuot`, the guard passes.
local macro "macroTest" : term => `(%%check_suppress%%)

-- A regular `def` body: `suppressInsideQuot` stays false in the quotation, so the guard fails
-- with the parser error captured in the expected output.
private def defTest : MacroM Syntax := `(%%check_suppress%%)
