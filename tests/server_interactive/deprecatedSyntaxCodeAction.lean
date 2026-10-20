/-!
Tests the code actions of `deprecated_syntax` replacement suggestions. Their info must be part of the
info tree of the deprecated command or tactic, which must still be reported for hovers and
incremental tactic elaboration.
-/

set_option linter.deprecated.syntax true

syntax (name := oldCheck) "#old_check " term : command
macro_rules | `(#old_check $e) => `(#check $e)

deprecated_syntax oldCheck "use `#check` instead" (since := "2026-10-19")
  | `(#old_check $e) => `(#check $e)

#old_check Nat
 --^ codeAction
           --^ textDocument/hover

syntax (name := oldExact) "old_exact " term : tactic
macro_rules | `(tactic| old_exact $e) => `(tactic| exact $e)

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)

example (h : True) : True := by old_exact h
                                --^ codeAction

syntax (name := oldNum) "old_num" : term
macro_rules | `(old_num) => `(42)

deprecated_syntax oldNum "use `42` instead" (since := "2026-10-19")
  | `(old_num) => `(42)

example : Nat := old_num
                 --^ codeAction
