/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.PropLemmas
/-!
# Specializations of basic logic lemmas

These are useful for `omega` while constructing proofs, but not considered generally useful
so are hidden in the `Lean.Omega` namespace.

If you find yourself needing them elsewhere, please move them first to another file.
-/

namespace Lean.Omega

theorem and_not_not_of_not_or (h : ¬ (p ∨ q)) : ¬ p ∧ ¬ q := not_or.mp h

theorem Decidable.or_not_not_of_not_and [Decidable p] [Decidable q]
    (h : ¬ (p ∧ q)) : ¬ p ∨ ¬ q :=
  Decidable.not_and_iff_or_not.mp h

theorem Decidable.and_or_not_and_not_of_iff {p q : Prop} [Decidable q] (h : p ↔ q) :
    (p ∧ q) ∨ (¬p ∧ ¬q) := Decidable.iff_iff_and_or_not_and_not.mp h

theorem Decidable.not_iff_iff_and_not_or_not_and [Decidable a] [Decidable b] :
    (¬ (a ↔ b)) ↔ (a ∧ ¬ b) ∨ ((¬ a) ∧ b) :=
  ⟨fun e => if hb : b then
    .inr ⟨fun ha => e ⟨fun _ => hb, fun _ => ha⟩, hb⟩
  else
    .inl ⟨if ha : a then ha else False.elim (e ⟨fun ha' => absurd ha' ha, fun hb' => absurd hb' hb⟩), hb⟩,
  Or.rec (And.rec fun ha nb w => nb (w.mp ha)) (And.rec fun na hb w => na (w.mpr hb))⟩

theorem Decidable.and_not_or_not_and_of_not_iff [Decidable a] [Decidable b]
    (h : ¬ (a ↔ b)) : a ∧ ¬b ∨ ¬a ∧ b :=
  Decidable.not_iff_iff_and_not_or_not_and.mp h

theorem Decidable.and_not_of_not_imp [Decidable a] (h : ¬(a → b)) : a ∧ ¬b :=
  Decidable.not_imp_iff_and_not.mp h

theorem ite_disjunction {α : Type u} {P : Prop} [Decidable P] {a b : α} :
    (P ∧ (if P then a else b) = a) ∨ (¬ P ∧ (if P then a else b) = b) :=
  if h : P then
    .inl ⟨h, if_pos h⟩
  else
    .inr ⟨h, if_neg h⟩

end Lean.Omega
