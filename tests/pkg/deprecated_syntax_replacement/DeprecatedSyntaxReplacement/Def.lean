module

/-!
Deprecates syntax with replacement alternatives in a module that imports only `Init`, for use from
`DeprecatedSyntaxReplacement.Use`.
-/

public section

syntax (name := oldExact) "old_exact " term : tactic
macro_rules | `(tactic| old_exact $e) => `(tactic| exact $e)

deprecated_syntax oldExact "use `exact` instead" (since := "2026-10-19")
  | `(tactic| old_exact $e) => `(tactic| exact $e)

syntax (name := oldNum) "old_num" : term
macro_rules | `(old_num) => `(42)

deprecated_syntax oldNum "use `42` instead" (since := "2026-10-19")
  | `(old_num) => `(42)
