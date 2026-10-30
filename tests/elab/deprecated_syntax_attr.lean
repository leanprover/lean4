import Lean

/-!
Tests that `@[deprecated]` on the commands that declare syntax (`syntax`, `macro`, `elab`,
`notation` and the mixfix commands) deprecates the declared syntax, like `deprecated_syntax`.
-/

set_option linter.deprecated true
set_option linter.deprecated.syntax true

@[deprecated "use `trivial` instead" (since := "2026-10-23")]
syntax (name := oldTriv) "old_triv" : tactic
macro_rules | `(tactic| old_triv) => `(tactic| trivial)

/--
warning: syntax 'oldTriv' has been deprecated: use `trivial` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : True := by old_triv

@[deprecated "use `1` instead" (since := "2026-10-23")]
macro "oldOne" : term => `(1)

/--
warning: syntax 'termOldOne' has been deprecated: use `1` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := oldOne

open Lean Elab Term in
@[deprecated "use `2` instead" (since := "2026-10-23")]
elab "oldTwo" : term => return mkNatLit 2

/--
warning: syntax 'termOldTwo' has been deprecated: use `2` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := oldTwo

@[deprecated "use `3` instead" (since := "2026-10-23")]
notation "oldThree" => 3

/--
warning: syntax 'termOldThree' has been deprecated: use `3` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := oldThree

@[deprecated "use `+` instead" (since := "2026-10-23")]
infixl:65 " +' " => Nat.add

/--
warning: syntax '«term_+'_»' has been deprecated: use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := 1 +' 2

-- Other attributes may be given alongside `@[deprecated]`.
@[inherit_doc Nat.succ, deprecated "use `Nat.succ` instead" (since := "2026-10-23")]
prefix:max "succ! " => Nat.succ

/--
warning: syntax 'termSucc!_' has been deprecated: use `Nat.succ` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := succ! 1

-- Scoped notation is deprecated where the scope is open.
namespace Scoped

@[deprecated "use `id` instead" (since := "2026-10-23")]
scoped prefix:max "id! " => id

end Scoped

open Scoped in
/--
warning: syntax 'Scoped.termId!_' has been deprecated: use `id` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := id! 1

-- The deprecation is reported when the syntax is used inside a quotation.
/--
warning: quotation uses deprecated syntax 'termOldThree': use `3` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
macro "usesOldThree" : term => ``(oldThree)

-- The `(since := "...")` clause is checked as for declarations.
/--
warning: `[deprecated]` attribute should specify the date or library version at which the deprecation was introduced, using `(since := "...")`
-/
#guard_msgs (substring := true) in
@[deprecated "use `4` instead"]
notation "oldFour" => 4

/--
warning: syntax 'termOldFour' has been deprecated: use `4` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := oldFour

-- Syntax has no declaration that could replace it.
/--
error: `[deprecated]` on syntax cannot specify a replacement declaration; describe the replacement in the deprecation message instead
-/
#guard_msgs in
@[deprecated Nat.add (since := "2026-10-23")]
notation "oldAdd" => Nat.add

-- A later `deprecated_syntax` command replaces the deprecation, here to add a replacement.
deprecated_syntax termOldOne "use the literal instead" (since := "2026-10-23")
  | `(oldOne) => `(1)

/--
warning: syntax 'termOldOne' has been deprecated: use the literal instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵O̵n̵e̵1̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := oldOne

-- Without `@[deprecated]`, the syntax is not deprecated.
notation "newFive" => 5

#guard_msgs in
example : Nat := newFive
