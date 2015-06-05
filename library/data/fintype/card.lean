/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Haitao Zhang

Cardinality for finite types.
-/
import .basic data.list data.finset.card
open eq.ops nat function list finset

namespace fintype

definition card [reducible] (A : Type) [finA : fintype A] := finset.card (@finset.univ A _)

lemma card_eq_card_image_of_inj
      {A : Type} [finA : fintype A] [deceqA : decidable_eq A]
      {B : Type} [finB : fintype B] [deceqB : decidable_eq B]
      {f : A → B} :
  injective f → finset.card (image f univ) = card A :=
assume Pinj,
card_image_eq_of_inj_on (to_set_univ⁻¹ ▸ (iff.mp !set.injective_iff_inj_on_univ Pinj))

-- General version of the pigeonhole principle. See also data.less_than.
lemma card_le_of_inj (A : Type) [finA : fintype A] [deceqA : decidable_eq A]
                     (B : Type) [finB : fintype B] [deceqB : decidable_eq B] :
   (∃ f : A → B, injective f) → card A ≤ card B :=
assume Pex, obtain f Pinj, from Pex,
assert Pinj_on_univ : _, from iff.mp !set.injective_iff_inj_on_univ Pinj,
assert Pinj_ts : _, from to_set_univ⁻¹ ▸ Pinj_on_univ,
assert Psub : (image f univ) ⊆ univ, from !subset_univ,
finset.card_le_of_inj_on univ univ (exists.intro f (and.intro Pinj_ts Psub))

-- used to prove that inj ∧ eq card => surj
lemma univ_of_card_eq_univ {A : Type} [finA : fintype A] [deceqA : decidable_eq A] {s : finset A} :
  finset.card s = card A → s = univ :=
assume Pcardeq, ext (take a,
assert D : decidable (a ∈ s), from decidable_mem a s, begin
apply iff.intro,
  intro ain, apply mem_univ,
  intro ain, cases D with Pin Pnin,
    exact Pin,
    assert Pplus1 : finset.card (insert a s) = finset.card s + 1,
      exact card_insert_of_not_mem Pnin,
    rewrite Pcardeq at Pplus1,
    assert Ple : finset.card (insert a s) ≤ card A,
      apply card_le_card_of_subset, apply subset_univ,
    rewrite Pplus1 at Ple,
    exact false.elim (not_succ_le_self Ple)
end)

end fintype
