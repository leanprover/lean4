/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura

Finite ordinal types.
-/
import data.list.basic data.finset.basic data.fintype.card
open eq.ops nat function list finset fintype

structure fin (n : nat) := (val : nat) (is_lt : val < n)
attribute fin.val [coercion]

definition less_than [reducible] := fin

namespace fin
section
open decidable
protected definition has_decidable_eq [instance] (n : nat) : ∀ (i j : fin n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
      match nat.has_decidable_eq ival jval with
      | inl veq := inl (by substvars)
      | inr vne := inr (by intro h; injection h; contradiction)
      end
end

lemma dinj_lt (n : nat) : dinj (λ i, i < n) fin.mk :=
take a1 a2 Pa1 Pa2 Pmkeq, fin.no_confusion Pmkeq (λ Pe Pqe, Pe)

lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i := rfl

definition upto [reducible] (n : nat) : list (fin n) :=
dmap (λ i, i < n) fin.mk (list.upto n)

lemma nodup_upto (n : nat) : nodup (upto n) :=
dmap_nodup_of_dinj (dinj_lt n) (list.nodup_upto n)

lemma mem_upto (n : nat) : ∀ (i : fin n), i ∈ upto n :=
take i, fin.destruct i
  (take ival Piltn,
    assert Pin : ival ∈ list.upto n, from mem_upto_of_lt Piltn,
    mem_dmap Piltn Pin)

lemma upto_zero : upto 0 = [] :=
by rewrite [↑upto, list.upto_nil, dmap_nil]

lemma map_val_upto (n : nat) : map fin.val (upto n) = list.upto n :=
map_dmap_of_inv_of_pos (val_mk n) (@lt_of_mem_upto n)

lemma length_upto (n : nat) : length (upto n) = n :=
calc
  length (upto n) = length (list.upto n) : (map_val_upto n ▸ length_map fin.val (upto n))⁻¹
              ... = n                    : list.length_upto n

definition is_fintype [instance] (n : nat) : fintype (fin n) :=
fintype.mk (upto n) (nodup_upto n) (mem_upto n)

section pigeonhole
open fintype

lemma card_fin (n : nat) : card (fin n) = n := length_upto n

theorem pigeonhole {n m : nat} (Pmltn : m < n) : ¬∃ f : fin n → fin m, injective f :=
assume Pex, absurd Pmltn (not_lt_of_ge
  (calc
       n = card (fin n) : card_fin
     ... ≤ card (fin m) : card_le_of_inj (fin n) (fin m) Pex
     ... = m : card_fin))

end pigeonhole

definition zero (n : nat) : fin (succ n) :=
mk 0 !zero_lt_succ

variable {n : nat}

theorem val_lt : ∀ i : fin n, val i < n
| (mk v h) := h

definition lift : fin n → Π m, fin (n + m)
| (mk v h) m := mk v (lt_add_of_lt_right h m)

theorem val_lift : ∀ (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m := rfl

definition pred : fin n → fin n
| (mk v h) := mk (nat.pred v) (pre_lt_of_lt h)

lemma val_pred : ∀ (i : fin n), val (pred i) = nat.pred (val i)
| (mk v h) := rfl

lemma pred_zero : pred (zero n) = zero n :=
rfl

definition mk_pred (i : nat) (h : succ i < succ n) : fin n :=
mk i (lt_of_succ_lt_succ h)

definition succ : fin n → fin (succ n)
| (mk v h) := mk (nat.succ v) (succ_lt_succ h)

lemma val_succ : ∀ (i : fin n), val (succ i) = nat.succ (val i)
| (mk v h) := rfl

definition elim0 {C : Type} : fin 0 → C
| (mk v h) := absurd h !not_lt_zero
end fin
