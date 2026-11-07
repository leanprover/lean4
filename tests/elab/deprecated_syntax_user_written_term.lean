import Lean

/-!
Tests that uses of deprecated term and `do` element syntax report only the syntax, not the
deprecated constants and syntax produced by its expansion, as `deprecated_syntax_user_written.lean`
tests for deprecated tactics. Deprecated constants and syntax written by the user in the arguments
of deprecated syntax are still reported.
-/

open Lean Elab Term

set_option linter.deprecated true
set_option linter.deprecated.syntax true

def newConst := 1

@[deprecated newConst (since := "2026-10-23")]
def oldConst := 1

@[deprecated Nat.add (since := "2026-10-23")]
def oldAdd (a b : Nat) := a + b

@[deprecated trivial (since := "2026-10-23")]
theorem oldTrue : True := trivial

namespace Class

@[deprecated "use `Class.inter` instead" (since := "2026-10-23")]
def sInter (x : Nat) : Nat := x

end Class

@[deprecated "use `newConst` instead" (since := "2026-10-23")]
notation (name := notationOld) "notation_old" => oldConst

@[deprecated "use `newConst + x` instead" (since := "2026-10-23")]
macro (name := macroOld) "macro_old " x:term:max : term => ``(oldConst + $x)

@[deprecated "use `+` instead" (since := "2026-10-23")]
infixl:65 (name := addOld) " +' " => oldAdd

namespace Foo

@[deprecated "use `⋂` instead" (since := "2026-10-23")]
scoped prefix:110 (name := sInterOld) "⋂₀ " => Class.sInter

end Foo

@[deprecated "use `newConst` instead" (since := "2026-10-23")]
macro (name := macroBodyOld) "macro_body_old" : term => ``(notation_old)

@[deprecated "use `newConst` instead" (since := "2026-10-23")]
elab (name := elabOld) "elab_old" : term => do
  elabTerm (← ``(oldConst)) none

@[deprecated "use `trivial` instead" (since := "2026-10-23")]
macro (name := byOld) "by_old" : term => `((by exact oldTrue : True))

@[deprecated "use `pure` instead" (since := "2026-10-23")]
syntax (name := doOld) "do_old " term : doElem

macro_rules | `(doElem| do_old $e) => `(doElem| pure (oldConst + $e))

@[deprecated "use `pure ()` instead" (since := "2026-10-23")]
syntax (name := doSkipOld) "do_skip_old" : doElem

macro_rules | `(doElem| do_skip_old) => `(doElem| pure ())

set_option linter.deprecated false in
notation (name := notationNew) "notation_new" => oldConst

/--
warning: syntax 'notationOld' has been deprecated: use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := notation_old

/--
warning: syntax 'macroOld' has been deprecated: use `newConst + x` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := macro_old 1

-- A deprecated constant written by the user in an argument is reported.
/--
warning: syntax 'macroOld' has been deprecated: use `newConst + x` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
example : Nat := macro_old oldConst

-- Deprecated syntax written by the user in an argument is reported.
/--
warning: syntax 'macroOld' has been deprecated: use `newConst + x` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'notationOld' has been deprecated: use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := macro_old notation_old

/--
warning: syntax 'addOld' has been deprecated: use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := 1 +' 2

open Foo in
/--
warning: syntax 'Foo.sInterOld' has been deprecated: use `⋂` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := ⋂₀ 3

open Foo in
/--
warning: syntax 'Foo.sInterOld' has been deprecated: use `⋂` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `Class.sInter` has been deprecated: use `Class.inter` instead
-/
#guard_msgs in
example : Nat := ⋂₀ (Class.sInter 3)

-- Deprecated syntax produced by the expansion of deprecated syntax is not reported.
/--
warning: syntax 'macroBodyOld' has been deprecated: use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := macro_body_old

/--
warning: syntax 'elabOld' has been deprecated: use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := elab_old

-- The tactic block produced by the expansion is elaborated after the expansion.
/--
warning: syntax 'byOld' has been deprecated: use `trivial` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : True := by_old

-- Operands of binary operators are expanded by the elaborator of the operator.
/--
warning: syntax 'notationOld' has been deprecated: use `newConst` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := 1 + notation_old

/--
warning: syntax 'doOld' has been deprecated: use `pure` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Id Nat := do do_old 1

/--
warning: syntax 'doOld' has been deprecated: use `pure` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldConst` has been deprecated: Use `newConst` instead

Hint: Replace the deprecated name:
  o̵l̵d̵n̲e̲w̲Const
-/
#guard_msgs in
example : Id Nat := do do_old oldConst

-- The rest of the `do` block is not part of the deprecated `do` element.
/--
warning: syntax 'doSkipOld' has been deprecated: use `pure ()` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: `oldConst` has been deprecated: Use `newConst` instead
-/
#guard_msgs in
example : Id Nat := do
  do_skip_old
  return notation_new
