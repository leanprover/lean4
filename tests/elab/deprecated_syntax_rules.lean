import Lean

/-!
Tests that, as for declarations marked `@[deprecated]` (RFC #8942), the rules of deprecated syntax
do not report the deprecated constants and syntax they refer to.
-/

open Lean Elab Term

set_option linter.deprecated true
set_option linter.deprecated.syntax true

def newConst := 1

@[deprecated newConst (since := "2026-10-23")]
def oldConst := 1

/-! Rules of syntax deprecated with `deprecated_syntax` -/

syntax (name := rulesOld) "rules_old" : term

deprecated_syntax rulesOld "use `newConst` instead" (since := "2026-10-23")

#guard_msgs in
macro_rules | `(rules_old) => ``(oldConst)

-- As in a deprecated declaration, enabling the linter inside the rules does not report them.
#guard_msgs in
macro_rules | `(rules_old) => set_option linter.deprecated true in ``(oldConst)

syntax (name := rulesIdentOld) "rules_ident_old" : term

deprecated_syntax rulesIdentOld "use `newConst` instead" (since := "2026-10-23")

#guard_msgs in
macro_rules (kind := rulesIdentOld) | _stx => ``(oldConst)

syntax (name := elabRulesOld) "elab_rules_old" : term

deprecated_syntax elabRulesOld "use `newConst` instead" (since := "2026-10-23")

#guard_msgs in
elab_rules : term | `(elab_rules_old) => do elabTerm (← ``(oldConst)) none

-- Rules of syntax that is not deprecated still report deprecated constants.
syntax (name := rulesNew) "rules_new" : term

/--
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
macro_rules | `(rules_new) => ``(oldConst)
