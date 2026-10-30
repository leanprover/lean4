import Lean

/-!
Tests that deprecated constants and syntax written by the user in the arguments of a deprecated
tactic are reported, while those produced by the expansion of the deprecated tactic are not.
-/

set_option linter.deprecated true
set_option linter.deprecated.syntax true

theorem newTrue : True := trivial

@[deprecated newTrue (since := "2026-10-21")]
theorem oldTrue : True := trivial

syntax (name := oldExact) "old_exact " term : tactic
macro_rules | `(tactic| old_exact $e) => `(tactic| exact $e)

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-21")

-- A deprecated constant written in the argument of a deprecated tactic is reported.
/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldTrue` has been deprecated: Use `newTrue` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲True
-/
#guard_msgs in
example : True := by old_exact oldTrue

-- Deprecated term syntax written in the argument of a deprecated tactic is reported.
syntax (name := oldTrueTerm) "old_true" : term
macro_rules | `(old_true) => `(newTrue)

deprecated_syntax oldTrueTerm "use `newTrue` instead" (since := "2026-10-21")

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'oldTrueTerm' has been deprecated: use `newTrue` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : True := by old_exact old_true

-- A deprecated constant produced by the expansion of a deprecated tactic is not reported.
syntax (name := oldTrivial) "old_trivial" : tactic
macro_rules | `(tactic| old_trivial) => `(tactic| exact oldTrue)

deprecated_syntax oldTrivial "use `exact newTrue` instead" (since := "2026-10-21")

/--
warning: syntax 'oldTrivial' has been deprecated: use `exact newTrue` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : True := by old_trivial

-- A deprecated tactic written in the argument of a deprecated tactic is reported, unlike the
-- deprecated `old_skip` produced by the expansion.
syntax (name := oldSkip) "old_skip" : tactic
macro_rules | `(tactic| old_skip) => `(tactic| skip)

deprecated_syntax oldSkip "use `skip` instead" (since := "2026-10-21")

syntax (name := oldSeq) "old_seq " tacticSeq : tactic
macro_rules | `(tactic| old_seq $seq) => `(tactic| (old_skip; ($seq)))

deprecated_syntax oldSeq "use `(...)` instead" (since := "2026-10-21")

/--
warning: syntax 'oldSeq' has been deprecated: use `(...)` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldTrue` has been deprecated: Use `newTrue` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲True
-/
#guard_msgs in
example : True := by old_seq old_exact oldTrue

-- The same applies to deprecated tactics implemented by an elaborator.
syntax (name := oldExactElab) "old_exact_elab " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| old_exact_elab $e) => do evalTactic (← `(tactic| (old_skip; exact $e)))

deprecated_syntax oldExactElab "use `exact` instead" (since := "2026-10-21")

/--
warning: syntax 'oldExactElab' has been deprecated: use `exact` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldTrue` has been deprecated: Use `newTrue` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲True
-/
#guard_msgs in
example : True := by old_exact_elab oldTrue

-- Deprecated theorems written as `grind` parameters are reported as well.
def foo : Nat := 0

theorem newFooEq : foo = 0 := rfl

@[deprecated newFooEq (since := "2026-10-21")]
theorem oldFooEq : foo = 0 := rfl

syntax (name := oldGrind) "old_grind " "[" ident "]" : tactic
macro_rules | `(tactic| old_grind [$i]) => `(tactic| grind [$i:ident])

deprecated_syntax oldGrind "use `grind` instead" (since := "2026-10-21")

/--
warning: syntax 'oldGrind' has been deprecated: use `grind` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldFooEq` has been deprecated: Use `newFooEq` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲FooEq
-/
#guard_msgs in
example : foo = 0 := by old_grind [oldFooEq]

-- The same applies to deprecated `grind` tactics.
variable {α : Type}

syntax (name := oldFinish) "old_finish" : grind
macro_rules | `(grind| old_finish) => `(grind| finish)

deprecated_syntax oldFinish "use `finish` instead" (since := "2026-10-21")

syntax (name := oldGrindSkip) "old_grind_skip" : grind
macro_rules | `(grind| old_grind_skip) => `(grind| skip)

deprecated_syntax oldGrindSkip "use `skip` instead" (since := "2026-10-21")

syntax (name := oldThen) "old_then " Lean.Parser.Tactic.Grind.grindSeq : grind
macro_rules | `(grind| old_then $seq) => `(grind| (old_grind_skip; ($seq)))

deprecated_syntax oldThen "use `(...)` instead" (since := "2026-10-21")

/--
warning: syntax 'oldThen' has been deprecated: use `(...)` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'oldFinish' has been deprecated: use `finish` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_then old_finish
