/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura

Finite ordinal types.
-/
import data.list.basic data.finset.basic data.fintype.card algebra.group
open eq.ops nat function list finset fintype

structure fin (n : nat) := (val : nat) (is_lt : val < n)

definition less_than [reducible] := fin

namespace fin

attribute fin.val [coercion]

section def_equal
variable {n : nat}

lemma eq_of_veq : ∀ {i j : fin n}, (val i) = j → i = j
| (mk iv ilt) (mk jv jlt) := assume (veq : iv = jv), begin congruence, assumption end

lemma veq_of_eq : ∀ {i j : fin n}, i = j → (val i) = j
| (mk iv ilt) (mk jv jlt) := assume Peq,
  have veq : iv = jv, from fin.no_confusion Peq (λ Pe Pqe, Pe), veq

lemma eq_iff_veq : ∀ {i j : fin n}, (val i) = j ↔ i = j :=
take i j, iff.intro eq_of_veq veq_of_eq

definition val_inj := @eq_of_veq n

end def_equal

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

definition lift_succ (i : fin n) : fin (nat.succ n) :=
lift i 1

definition maxi [reducible] : fin (succ n) :=
mk n !lt_succ_self

theorem val_lift : ∀ (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m := rfl

section lift_lower

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ maxi :=
by intro hlt he; substvars; exact absurd hlt (lt.irrefl n)

lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ maxi → i < n :=
assume hne  : i ≠ maxi,
assert visn : val i < nat.succ n, from val_lt i,
assert aux  : val (@maxi n) = n,   from rfl,
assert vne  : val i ≠ n, from
  assume he,
    have vivm : val i = val (@maxi n), from he ⬝ aux⁻¹,
    absurd (eq_of_veq vivm) hne,
lt_of_le_of_ne (le_of_lt_succ visn) vne

lemma lift_succ_ne_max {i : fin n} : lift_succ i ≠ maxi :=
begin
  cases i with v hlt, esimp [lift_succ, lift, max], intro he,
  injection he, substvars,
  exact absurd hlt (lt.irrefl v)
end

lemma lift_succ_inj : injective (@lift_succ n) :=
take i j, destruct i (destruct j (take iv ilt jv jlt Pmkeq,
  begin congruence, apply fin.no_confusion Pmkeq, intros, assumption end))

lemma lt_of_inj_of_max (f : fin (succ n) → fin (succ n)) :
  injective f → (f maxi = maxi) → ∀ i, i < n → f i < n :=
assume Pinj Peq, take i, assume Pilt,
assert P1 : f i = f maxi → i = maxi, from assume Peq, Pinj i maxi Peq,
have P : f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max P

definition lift_fun : (fin n → fin n) → (fin (succ n) → fin (succ n)) :=
λ f i, dite (i = maxi) (λ Pe, maxi) (λ Pne, lift_succ (f (mk i (lt_max_of_ne_max Pne))))

definition lower_inj (f : fin (succ n) → fin (succ n)) (inj : injective f) :
  f maxi = maxi → fin n → fin n :=
assume Peq, take i, mk (f (lift_succ i)) (lt_of_inj_of_max f inj Peq (lift_succ i) (lt_max_of_ne_max lift_succ_ne_max))

lemma lift_fun_max {f : fin n → fin n} : lift_fun f maxi = maxi :=
begin rewrite [↑lift_fun, dif_pos rfl] end

lemma lift_fun_of_ne_max {f : fin n → fin n} {i} (Pne : i ≠ maxi) :
  lift_fun f i = lift_succ (f (mk i (lt_max_of_ne_max Pne))) :=
begin rewrite [↑lift_fun, dif_neg Pne] end

lemma lift_fun_eq {f : fin n → fin n} {i : fin n} :
  lift_fun f (lift_succ i) = lift_succ (f i) :=
begin
rewrite [lift_fun_of_ne_max lift_succ_ne_max], congruence, congruence,
rewrite [-eq_iff_veq], esimp, rewrite [↑lift_succ, -val_lift]
end

lemma lift_fun_of_inj {f : fin n → fin n} : injective f → injective (lift_fun f) :=
assume Pinj, take i j,
assert Pdi : decidable (i = maxi), from _, assert Pdj : decidable (j = maxi), from _,
begin
  cases Pdi with Pimax Pinmax,
    cases Pdj with Pjmax Pjnmax,
      substvars, intros, exact rfl,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pjnmax],
        intro Plmax, apply absurd Plmax⁻¹ lift_succ_ne_max,
    cases Pdj with Pjmax Pjnmax,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pinmax],
        intro Plmax, apply absurd Plmax lift_succ_ne_max,
      rewrite [lift_fun_of_ne_max Pinmax, lift_fun_of_ne_max Pjnmax],
        intro Peq, rewrite [-eq_iff_veq],
        exact veq_of_eq (Pinj (lift_succ_inj Peq))
end

lemma lift_fun_inj : injective (@lift_fun n) :=
take f₁ f₂ Peq, funext (λ i,
assert Peqi : lift_fun f₁ (lift_succ i) = lift_fun f₂ (lift_succ i), from congr_fun Peq _,
begin revert Peqi, rewrite [*lift_fun_eq], apply lift_succ_inj end)

lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)) :=
by rewrite [↑lower_inj]

end lift_lower

section madd

definition madd (i j : fin (succ n)) : fin (succ n) :=
mk ((i + j) mod (succ n)) (mod_lt _ !zero_lt_succ)

lemma val_madd : ∀ i j : fin (succ n), val (madd i j) = (i + j) mod (succ n)
| (mk iv ilt) (mk jv jlt) := by esimp

lemma madd_inj : ∀ {i : fin (succ n)}, injective (madd i)
| (mk iv ilt) :=
take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (λ jv₁ jlt₁ jv₂ jlt₂, begin
  rewrite [↑madd, -eq_iff_veq],
  intro Peq, congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_mod_of_add_mod_eq_add_mod_left Peq
end))

lemma val_mod : ∀ i : fin (succ n), (val i) mod (succ n) = val i
| (mk iv ilt) := by esimp; rewrite [(mod_eq_of_lt ilt)]

definition minv : ∀ i : fin (succ n), fin (succ n)
| (mk iv ilt) := mk ((succ n - iv) mod succ n) (mod_lt _ !zero_lt_succ)

lemma madd_comm (i j : fin (succ n)) : madd i j = madd j i :=
by apply eq_of_veq; rewrite [*val_madd, add.comm (val i)]

lemma zero_madd (i : fin (succ n)) : madd (zero n) i = i :=
by apply eq_of_veq; rewrite [val_madd, ↑zero, nat.zero_add, mod_eq_of_lt (is_lt i)]

lemma madd_zero (i : fin (succ n)) : madd i (zero n) = i :=
!madd_comm ▸ zero_madd i

lemma madd_assoc (i j k : fin (succ n)) : madd (madd i j) k = madd i (madd j k) :=
by apply eq_of_veq; rewrite [*val_madd, mod_add_mod, add_mod_mod, add.assoc (val i)]

lemma madd_left_inv : ∀ i : fin (succ n), madd (minv i) i = zero n
| (mk iv ilt) := eq_of_veq (by
  rewrite [val_madd, ↑minv, ↑zero, mod_add_mod, sub_add_cancel (le_of_lt ilt), mod_self])

open algebra

definition madd_is_comm_group [instance] : add_comm_group (fin (succ n)) :=
add_comm_group.mk madd madd_assoc (zero n) zero_madd madd_zero minv madd_left_inv madd_comm

end madd

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

definition elim0 {C : fin 0 → Type} : Π i : fin 0, C i
| (mk v h) := absurd h !not_lt_zero

definition zero_succ_cases {C : fin (nat.succ n) → Type} :
  C (zero n) → (Π j : fin n, C (succ j)) → (Π k : fin (nat.succ n), C k) :=
begin
  intros CO CS k,
  induction k with [vk, pk],
  induction (nat.decidable_lt 0 vk) with [HT, HF],
  { show C (mk vk pk), from
    let vj := nat.pred vk in
    have HSv : vk = nat.succ vj, from
      eq.symm (succ_pred_of_pos HT),
    assert pj : vj < n, from
      lt_of_succ_lt_succ (eq.subst HSv pk),
    have HS : succ (mk vj pj) = mk vk pk, from
      val_inj (eq.symm HSv),
    eq.rec_on HS (CS (mk vj pj)) },
  { show C (mk vk pk), from
    have HOv : vk = 0, from
      eq_zero_of_le_zero (le_of_not_gt HF),
    have HO : zero n = mk vk pk, from
      val_inj (eq.symm HOv),
    eq.rec_on HO CO }
end

theorem choice {C : fin n → Type} :
  (∀ i : fin n, nonempty (C i)) → nonempty (Π i : fin n, C i) :=
begin
  revert C,
  induction n with [n, IH],
  { intros C H,
    apply nonempty.intro,
    exact elim0 },
  { intros C H,
    fapply nonempty.elim (H (zero n)),
    intro CO,
    fapply nonempty.elim (IH (λ i, C (succ i)) (λ i, H (succ i))),
    intro CS,
    apply nonempty.intro,
    exact zero_succ_cases CO CS }
end

end fin
