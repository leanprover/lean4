/-!
Tests that deprecated syntax is reported where elaborators expand macros themselves instead of
elaborating the syntax with `elabTerm`: operands of `binop%` and related elaborators, `do`
elements, patterns and syntax definitions.
-/

set_option linter.deprecated.syntax true

syntax (name := oldAdd) "old_add " term:max term:max : term
macro_rules | `(old_add $a $b) => `($a + $b)

deprecated_syntax oldAdd "use `+` instead" (since := "2026-10-19")

syntax:max (name := oldSucc) "old_succ " term:max : term
macro_rules | `(old_succ $e) => `(Nat.succ $e)

deprecated_syntax oldSucc "use `Nat.succ` instead" (since := "2026-10-19")

syntax:max (name := oldNeg) "old_neg " term:max : term
macro_rules | `(old_neg $e) => `(-$e)

deprecated_syntax oldNeg "use `-` instead" (since := "2026-10-19")

syntax (name := oldZero) "old_zero" : term
macro_rules | `(old_zero) => `(Nat.zero)

deprecated_syntax oldZero "use `Nat.zero` instead" (since := "2026-10-19")

/-! ## Operands of `binop%`, `unop%` and `binrel%` -/

/--
warning: syntax 'oldAdd' has been deprecated: use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1 + 2) * 3 : Nat
-/
#guard_msgs in
#check old_add 1 2 * 3

/--
warning: syntax 'oldNeg' has been deprecated: use `-` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: - -1 : Int
-/
#guard_msgs in
#check -old_neg (1 : Int)

/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: Nat.succ 1 = 2 : Prop
-/
#guard_msgs in
#check old_succ 1 = 2

syntax:65 (name := oldPlus) term:65 " +' " term:66 : term
macro_rules | `($a +' $b) => `($a + $b)

deprecated_syntax oldPlus "use `+` instead" (since := "2026-10-19")

syntax:50 (name := oldLe) term:51 " ≤' " term:51 : term
macro_rules | `($a ≤' $b) => `($a ≤ $b)

deprecated_syntax oldLe "use `≤` instead" (since := "2026-10-19")

-- Deprecated syntax nested in deprecated syntax is reported as well.
/--
warning: syntax 'oldLe' has been deprecated: use `≤` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
warning: syntax 'oldPlus' has been deprecated: use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: (1 + 2 ≤ 3) = True : Prop
-/
#guard_msgs in
#check (1 +' 2 ≤' 3) = True

macro "wrapped_add" : term => `(old_add 1 2)

/--
warning: macro 'termWrapped_add' (expanded from '«term_+_»') produces deprecated syntax 'oldAdd': use `+` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
---
info: 1 + 2 + 3 : Nat
-/
#guard_msgs in
#check wrapped_add + 3

-- Deprecated syntax is not reported in deprecated declarations.
#guard_msgs in
@[deprecated "use `+` instead" (since := "2026-10-19")]
def deprecatedAdd : Nat := old_add 1 2 * 3

/-! ## `do` elements -/

syntax (name := oldReturn) "old_return " term : doElem
macro_rules | `(doElem| old_return $e) => `(doElem| return $e)

deprecated_syntax oldReturn "use `return` instead" (since := "2026-10-19")

/--
warning: syntax 'oldReturn' has been deprecated: use `return` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def doReturnTest : Id Nat := do
  old_return 1

/-! ## Patterns -/

/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def patternTest : Nat → Nat
  | old_succ n => n
  | _ => 0

/--
warning: syntax 'oldZero' has been deprecated: use `Nat.zero` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def doMatchTest (n : Nat) : Id Nat := do
  match n with
  | old_zero => return 1
  | _ => return 0

macro "zero_pat" : term => `(old_zero)

/--
warning: macro 'termZero_pat' produces deprecated syntax 'oldZero': use `Nat.zero` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def macroPatternTest : Nat → Nat
  | zero_pat => 1
  | _ => 0

-- Elaboration of the `match` is postponed until the type of `n` is known.
/--
warning: syntax 'oldSucc' has been deprecated: use `Nat.succ` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat → Nat := (fun n => match n with | old_succ k => k | _ => 0 : _ → Nat)

/-! ## Syntax definitions -/

syntax:arg (name := oldMany) stx:max "*'" : stx
macro_rules | `(stx| $p*') => `(stx| $p*)

deprecated_syntax oldMany "use `*` instead" (since := "2026-10-19")

/--
warning: syntax 'oldMany' has been deprecated: use `*` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
syntax "nums " num*' : term

/--
warning: syntax 'oldMany' has been deprecated: use `*` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
macro "nums' " num*' : term => `(0)

/-! ## `do` elements implemented by an elaborator -/

deprecated_syntax Lean.Parser.Term.doUnless "use `if` instead" (since := "2026-10-19")

/--
warning: syntax 'Lean.Parser.Term.doUnless' has been deprecated: use `if` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def doUnlessTest (b : Bool) : Id Nat := do
  unless b do
    return 1
  return 2

-- Nested actions are lifted out of the syntax before it is elaborated, and it is reported once.
/--
warning: syntax 'Lean.Parser.Term.doUnless' has been deprecated: use `if` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
def doUnlessNestedTest (b : Id Bool) : Id Nat := do
  unless (← b) do
    return 1
  return 2
