-- Enable the deprecated syntax linter (test framework disables all linters)
set_option linter.deprecated.syntax true

-- Test 1: Direct usage of deprecated term syntax → warning
deprecated_syntax Lean.Parser.Term.let_fun "use `have` instead" (since := "2026-03-24")

-- Note: the paren macro expands to the inner expression, so the warning
-- is attributed to the paren macro call site
#check (let_fun x := 1; x)

/--
  Test 2: Macro that expands to deprecated syntax → warning at macro call site
  It will not warn at macro definition, as it is defined via
  single backtick and hence does not trigger a pre-check.
-/
syntax "my_wrapper " : term
macro_rules | `(my_wrapper) => `(let_fun x := 1; x)

#check (my_wrapper)

-- Test 2b: Nested macros — A expands to B, B expands to deprecated syntax.
-- Warning names immediate producer (innerMacro) and its caller (outerMacro).
syntax "innerMacro " : term
macro_rules | `(innerMacro) => `(let_fun x := 1; x)
syntax "outerMacro " : term
macro_rules | `(outerMacro) => `(innerMacro)

-- Use `let` binding to avoid parens adding another macro layer
def nested_test := outerMacro

-- Test 3: set_option linter.deprecated.syntax false suppresses warnings
set_option linter.deprecated.syntax false in
#check (let_fun x := 1; x)

-- Test 4: Non-deprecated syntax → no warning
#check (42 : Nat)

-- Test 5: deprecated_syntax for a tactic
syntax "myDepTac" : tactic
macro_rules | `(tactic| myDepTac) => `(tactic| trivial)

deprecated_syntax tacticMyDepTac "use `trivial` instead" (since := "2026-03-24")

example : True := by myDepTac

-- Test 6: Quotation precheck warns at macro definition time
-- Define a custom syntax, give it a macro expansion, then deprecate it
syntax "oldThing" : term
macro_rules | `(oldThing) => `(42)
deprecated_syntax termOldThing "use `42` instead" (since := "2026-03-24")

-- A macro whose RHS quotation uses the deprecated syntax → warning at definition site
syntax "usesOld " : term
macro_rules | `(usesOld) => ``(oldThing)

-- Test 7: set_option linter.deprecated.syntax false suppresses quotation precheck warning
syntax "usesOld2 " : term
set_option linter.deprecated.syntax false in
macro_rules | `(usesOld2) => ``(oldThing)

-- Test 8: Quotation that does NOT use deprecated syntax → no warning
syntax "usesNew " : term
macro_rules | `(usesNew) => ``(42)

-- Test 9: deprecated_syntax for a command — direct usage
syntax "myDepCmd " : command
macro_rules | `(myDepCmd) => `(#check 42)

deprecated_syntax commandMyDepCmd "use `#check` instead" (since := "2026-03-24")

myDepCmd

-- Test 9b: Macro that expands to deprecated command → warning at macro call site
syntax "myWrapperCmd " : command
macro_rules | `(myWrapperCmd) => `(myDepCmd)

myWrapperCmd

-- Test 9c: set_option linter.deprecated.syntax false suppresses command warning
set_option linter.deprecated.syntax false in
myDepCmd

-- Test 10: missing since emits a warning
deprecated_syntax Lean.Parser.Term.show
