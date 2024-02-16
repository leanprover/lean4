/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

/-!
# Specializations of basic logic lemmas

These are useful for `omega` while constructing proofs, but not considered generally useful
so are hidden in the `Std.Tactic.Omega` namespace.

If you find yourself needing them elsewhere, please move them first to another file.
-/

namespace Lean.Elab.Tactic.Omega

theorem and_not_not_of_not_or (h : ¬ (p ∨ q)) : ¬ p ∧ ¬ q := not_or.mp h

theorem Decidable.or_not_not_of_not_and [Decidable p] [Decidable q]
    (h : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
  (Decidable.not_and_iff_or_not _ _).mp h

theorem Decidable.and_or_not_and_not_of_iff [Decidable q] (h : p ↔ q) :
    (p ∧ q) ∨ (¬p ∧ ¬q) := Decidable.iff_iff_and_or_not_and_not.mp h

theorem Decidable.not_iff_iff_and_not_or_not_and [Decidable a] [Decidable b] :
    (¬ (a ↔ b)) ↔ (a ∧ ¬ b) ∨ ((¬ a) ∧ b) := by
  by_cases b <;> simp_all [Decidable.not_not]

theorem Decidable.and_not_or_not_and_of_not_iff [Decidable a] [Decidable b]
    (h : ¬ (a ↔ b)) : a ∧ ¬b ∨ ¬a ∧ b :=
  Decidable.not_iff_iff_and_not_or_not_and.mp h

theorem Decidable.and_not_of_not_imp [Decidable a] (h : ¬(a → b)) : a ∧ ¬b :=
  Decidable.not_imp_iff_and_not.mp h

end Lean.Elab.Tactic.Omega
