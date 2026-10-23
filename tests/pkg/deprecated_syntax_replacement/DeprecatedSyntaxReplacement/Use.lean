module

import DeprecatedSyntaxReplacement.Def

/-!
Tests that replacement suggestions of `deprecated_syntax` work across modules.
-/

set_option linter.deprecated.syntax true

/--
warning: syntax 'oldExact' has been deprecated: use `exact` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵exact h

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (h : True) : True := by old_exact h

/--
warning: syntax 'oldNum' has been deprecated: use `42` instead

Hint: Replace the deprecated syntax:
  o̵l̵d̵_̵n̵u̵m̵4̲2̲

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example : Nat := old_num
