module

/-!
Tests that the deprecated syntax linter warns directly at deprecated syntax written inside a
namespaced declaration (`theorem Foo.bar ...`). Such declarations are internally expanded via a
macro into a `namespace` block; the warning must not be attributed to that macro expansion, but
behave exactly as in the non-namespaced case.
-/

set_option linter.deprecated.syntax true

syntax (name := deprecatedProofTactic) "deprecated_proof_tactic" : tactic
macro_rules
  | `(tactic| deprecated_proof_tactic) => `(tactic| trivial)

deprecated_syntax deprecatedProofTactic "use `trivial` instead" (since := "2026-08-27")

/--
warning: syntax 'deprecatedProofTactic' has been deprecated: use `trivial` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
theorem DeprecatedSyntax.namespacedTheorem : True := by
  deprecated_proof_tactic

/--
warning: syntax 'deprecatedProofTactic' has been deprecated: use `trivial` instead

Note: This linter can be disabled with `set_option linter.deprecated.syntax false`
-/
#guard_msgs in
theorem nonNamespacedTheorem : True := by
  deprecated_proof_tactic
