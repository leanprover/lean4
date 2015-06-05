/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Haitao Zhang

Finite ordinal types.
-/
import data.list.basic data.finset.basic data.fintype.card
open eq.ops nat function list finset fintype

structure less_than (n : nat) := (val : nat) (is_lt : val < n)
attribute less_than.val [coercion]

namespace less_than

section
open decidable
protected definition has_decidable_eq [instance] (n : nat) : ∀ (i j : less_than n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
      match nat.has_decidable_eq ival jval with
      | inl veq := inl (by substvars)
      | inr vne := inr (by intro h; injection h; contradiction)
      end
end

lemma dinj_lt (n : nat) : dinj (λ i, i < n) less_than.mk :=
take a1 a2 Pa1 Pa2 Pmkeq, less_than.no_confusion Pmkeq (λ Pe Pqe, Pe)

lemma val_mk (n i : nat) (Plt : i < n) : less_than.val (less_than.mk i Plt) = i := rfl

definition upto [reducible] (n : nat) : list (less_than n) :=
dmap (λ i, i < n) less_than.mk (list.upto n)

lemma nodup_upto (n : nat) : nodup (upto n) :=
dmap_nodup_of_dinj (dinj_lt n) (list.nodup_upto n)

lemma mem_upto (n : nat) : ∀ (i : less_than n), i ∈ upto n :=
take i, less_than.destruct i
  (take ival Piltn,
    assert Pin : ival ∈ list.upto n, from mem_upto_of_lt Piltn,
    mem_of_dmap Piltn Pin)

lemma upto_zero : upto 0 = [] :=
by rewrite [↑upto, list.upto_nil, dmap_nil]

lemma map_val_upto (n : nat) : map less_than.val (upto n) = list.upto n :=
map_of_dmap_inv_pos (val_mk n) (@lt_of_mem_upto n)

lemma length_upto (n : nat) : length (upto n) = n :=
calc
  length (upto n) = length (list.upto n) : (map_val_upto n ▸ length_map less_than.val (upto n))⁻¹
              ... = n                    : list.length_upto n

definition fintype_less_than [instance] (n : nat) : fintype (less_than n) :=
fintype.mk (upto n) (nodup_upto n) (mem_upto n)

section pigeonhole
open fintype

lemma card_less_than (n : nat) : card (less_than n) = n := length_upto n

theorem pigeonhole {n m : nat} (Pmltn : m < n) : ¬ (∃ f : less_than n → less_than m, injective f) :=
not.intro
  (assume Pex, absurd Pmltn (not_lt_of_ge
    (calc
        n = card (less_than n) : card_less_than
      ... ≤ card (less_than m) : card_le_of_inj (less_than n) (less_than m) Pex
      ... = m : card_less_than)))

end pigeonhole

end less_than
