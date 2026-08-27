module

/-! # Tests for the `unusedDecidableInType` linter.

These exercise `linter.extra.unusedDecidableInType`, which warns when a theorem's hypotheses
include `Decidable*` instances that are not used in the remainder of the type. -/

set_option linter.extra.unusedDecidableInType true

variable (α : Type)

-- A theorem that doesn't use a `[DecidableEq α]` hypothesis at all.
/--
warning: `unusedEq` does not use the following hypothesis in its type:
  • [DecidableEq α] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.extra.unusedDecidableInType false`
-/
#guard_msgs in
theorem unusedEq [DecidableEq α] : True := trivial

-- A theorem that doesn't use a `[Decidable p]` hypothesis at all.
/--
warning: `unusedDecidable` does not use the following hypothesis in its type:
  • [Decidable p] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.extra.unusedDecidableInType false`
-/
#guard_msgs in
theorem unusedDecidable (p : Prop) [Decidable p] : True := trivial

-- Multiple unused `Decidable*` hypotheses are reported together.
/--
warning: `unusedMulti` does not use the following hypotheses in its type:
  • [DecidableRel r] (#4)
  • [DecidablePred q] (#5)

Consider removing these hypotheses and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.extra.unusedDecidableInType false`
-/
#guard_msgs in
theorem unusedMulti (r : α → α → Prop) (q : α → Prop) [DecidableRel r] [DecidablePred q] :
    True := trivial

-- The `[DecidableEq α]` hypothesis is used in the type, so no warning.
#guard_msgs in
theorem usedEq [DecidableEq α] (a b : α) : decide (a = b) = decide (a = b) := rfl

-- The `[Decidable p]` hypothesis is used only in the proof body, so the linter still warns.
/--
warning: `usedOnlyInProof` does not use the following hypothesis in its type:
  • [Decidable p] (#2)

Consider removing this hypothesis and using `classical` in the proof instead. For terms, consider using `open scoped Classical in` at the term level (not the command level).

Note: This linter can be disabled with `set_option linter.extra.unusedDecidableInType false`
-/
#guard_msgs in
theorem usedOnlyInProof (p : Prop) [Decidable p] : True := by
  if _ : p then trivial else trivial

-- Theorems in the `Decidable` namespace are exempt.
#guard_msgs in
theorem Decidable.exemptByNamespace [DecidableEq α] : True := trivial

-- Disabling the linter silences the warning.
#guard_msgs in
set_option linter.extra.unusedDecidableInType false in
theorem silenced [DecidableEq α] : True := trivial
