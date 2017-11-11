/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.data.ordering init.data.nat.lemmas init.ite_simp

lemma nat.cmp_lt.trans (a b c : nat) : a <_cmp b → b <_cmp c → a <_cmp c :=
by simp [cmp_lt, cmp, nat.cmp]; apply nat.lt_trans

lemma nat.cmp_lt.irrefl (a : nat) : ¬ a <_cmp a :=
by simp [cmp_lt, cmp, nat.cmp]; apply nat.lt_irrefl

lemma nat.cmp_lt.incomp_trans (a b c : nat) : (¬ a <_cmp b ∧ ¬ b <_cmp a) → (¬ b <_cmp c ∧ ¬ c <_cmp b) → (¬ a <_cmp c ∧ ¬ c <_cmp a) :=
begin
  simp [cmp_lt, cmp, nat.cmp],
  intros h₁ h₃,
  cases h₁ with h₁ h₂,
  cases h₃ with h₃ h₄,
  have lba : b ≤ a, from le_of_not_gt h₁,
  have lab : a ≤ b, from le_of_not_gt h₂,
  have lcb : c ≤ b, from le_of_not_gt h₃,
  have lbc : b ≤ c, from le_of_not_gt h₄,
  have lac : a ≤ c, from le_trans lab lbc,
  have lca : c ≤ a, from le_trans lcb lba,
  exact ⟨not_lt_of_ge lca, not_lt_of_ge lac⟩
end

lemma nat.cmp_lt_iff_cmp_gt (a b : nat) : a <_cmp b ↔ b >_cmp a :=
begin
  simp [cmp_lt, cmp_gt, cmp, nat.cmp],
  apply iff.intro,
  { intro h, split,
    { intro h₁, subst h₁, exact absurd h (lt_irrefl _) },
    { apply not_lt_of_gt h} },
  { intro h, cases h with h₁ h₂, apply lt_of_le_of_ne (le_of_not_gt h₂) (ne.symm h₁) }
end

lemma nat.cmp_lt_incomp_iff_cmp_eq (a b : nat) : (¬ a <_cmp b ∧ ¬ b <_cmp a) ↔ a =_cmp b :=
begin
  simp [cmp_lt, cmp_eq, cmp, nat.cmp],
  apply iff.intro,
  { intro h, cases h, split,
    { apply le_antisymm, repeat {apply le_of_not_gt, assumption } },
    { assumption } },
  { intro h, cases h, split,
    { assumption },
    { apply not_lt_of_ge, subst a, apply le_refl } }
end

instance : has_strict_weak_ordering nat :=
{ cmp              := nat.cmp,
  irrefl           := nat.cmp_lt.irrefl,
  trans            := nat.cmp_lt.trans,
  incomp_trans     := nat.cmp_lt.incomp_trans,
  lt_iff_gt        := nat.cmp_lt_iff_cmp_gt,
  incomp_iff_eq    := nat.cmp_lt_incomp_iff_cmp_eq }
