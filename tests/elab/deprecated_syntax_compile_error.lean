module

import Lean

/-!
Tests that a compilation error in a `deprecated_syntax` replacement preserves the previous
deprecation message and replacement.
-/

set_option linter.deprecated.syntax true

syntax (name := oldNum) "old_num" : term
macro_rules | `(old_num) => `(42)

deprecated_syntax oldNum "use `42` instead" (since := "2026-10-23")
  | _ => `(42)

def nonmetaReplacement : Lean.Macro := fun _ => `(43)

/--
error: Invalid `meta` definition `_aux_elab_deprecated_syntax_compile_error___deprecatedSyntax_oldNum_2`, `nonmetaReplacement` not marked `meta`
-/
#guard_msgs in
deprecated_syntax oldNum "use `43` instead" (since := "2026-10-23")
  | stx => nonmetaReplacement stx

/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵n̵u̵m̵4̲2̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := old_num
