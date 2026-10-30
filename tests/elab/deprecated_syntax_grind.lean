/-!
Tests that deprecated syntax is reported in `grind` interactive mode, like in regular tactic blocks.
-/

set_option linter.deprecated.syntax true

variable {α : Type}

syntax (name := oldFinish) "old_finish" : grind
macro_rules | `(grind| old_finish) => `(grind| finish)

deprecated_syntax oldFinish "use `finish` instead" (since := "2026-10-20")

/--
warning: syntax 'oldFinish' has been deprecated: use `finish` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_finish

-- A deprecated grind tactic warns once, although its expansion uses itself and `old_finish`.
syntax (name := oldRec) "old_rec " num : grind
macro_rules
  | `(grind| old_rec 0) => `(grind| old_finish)
  | `(grind| old_rec $n) => `(grind| old_rec $(Lean.quote (n.getNat - 1)))

deprecated_syntax oldRec "use `finish` instead" (since := "2026-10-20")

/--
warning: syntax 'oldRec' has been deprecated: use `finish` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_rec 2

-- A macro expanding to deprecated syntax warns at its call site.
macro "wraps_old_finish" : grind => `(grind| old_finish)

/--
warning: syntax 'oldFinish' has been deprecated: use `finish` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind => wraps_old_finish

-- Grind tactics implemented by an elaborator are reported as well.
deprecated_syntax Lean.Parser.Tactic.Grind.done "use `finish` instead" (since := "2026-10-20")

/--
warning: syntax 'Lean.Parser.Tactic.Grind.done' has been deprecated: use `finish` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
example (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind =>
    finish
    done

-- Deprecated syntax is not reported in deprecated declarations.
#guard_msgs in
@[deprecated "use something else" (since := "2026-10-20")]
theorem deprecatedUsesOldFinish (op : α → α → α) [Std.Associative op] (a b c d : α) :
    d = op b c → op a d = op (op a b) c := by
  grind => old_finish
