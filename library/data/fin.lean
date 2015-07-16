/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura

Finite ordinal types.
-/
import data.list.basic data.finset.basic data.fintype.card algebra.group data.equiv
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
  show iv = jv, from fin.no_confusion Peq (λ Pe Pqe, Pe)

lemma eq_iff_veq {i j : fin n} : (val i) = j ↔ i = j :=
iff.intro eq_of_veq veq_of_eq

definition val_inj := @eq_of_veq n

end def_equal

section
open decidable
protected definition has_decidable_eq [instance] (n : nat) : ∀ (i j : fin n), decidable (i = j)
| (mk ival ilt) (mk jval jlt) :=
  decidable_of_decidable_of_iff (nat.has_decidable_eq ival jval) eq_iff_veq
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
    assert ival ∈ list.upto n, from mem_upto_of_lt Piltn,
    mem_dmap Piltn this)

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

definition mk_mod [reducible] (n i : nat) : fin (succ n) :=
mk (i mod (succ n)) (mod_lt _ !zero_lt_succ)

variable {n : nat}

theorem val_lt : ∀ i : fin n, val i < n
| (mk v h) := h

lemma max_lt (i j : fin n) : max i j < n :=
max_lt (is_lt i) (is_lt j)

definition lift : fin n → Π m, fin (n + m)
| (mk v h) m := mk v (lt_add_of_lt_right h m)

definition lift_succ (i : fin n) : fin (nat.succ n) :=
lift i 1

definition maxi [reducible] : fin (succ n) :=
mk n !lt_succ_self

theorem val_lift : ∀ (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m := rfl

lemma mk_succ_ne_zero {i : nat} : ∀ {P}, mk (succ i) P ≠ zero n :=
assume P Pe, absurd (veq_of_eq Pe) !succ_ne_zero

lemma mk_mod_eq {i : fin (succ n)} : i = mk_mod n i :=
eq_of_veq begin rewrite [↑mk_mod, mod_eq_of_lt !is_lt] end

lemma mk_mod_of_lt {i : nat} (Plt : i < succ n) : mk_mod n i = mk i Plt :=
begin esimp [mk_mod], congruence, exact mod_eq_of_lt Plt end

section lift_lower

lemma lift_zero : lift_succ (zero n) = zero (succ n) := rfl

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ maxi :=
by intro hlt he; substvars; exact absurd hlt (lt.irrefl n)

lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ maxi → i < n :=
assume hne  : i ≠ maxi,
assert vne  : val i ≠ n, from
  assume he,
    have val (@maxi n) = n,   from rfl,
    have val i = val (@maxi n), from he ⬝ this⁻¹,
    absurd (eq_of_veq this) hne,
have val i < nat.succ n, from val_lt i,
lt_of_le_of_ne (le_of_lt_succ this) vne

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
have f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max this

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
assert lift_fun f₁ (lift_succ i) = lift_fun f₂ (lift_succ i), from congr_fun Peq _,
begin revert this, rewrite [*lift_fun_eq], apply lift_succ_inj end)

lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)) :=
by rewrite [↑lower_inj]

end lift_lower

section madd

definition madd (i j : fin (succ n)) : fin (succ n) :=
mk ((i + j) mod (succ n)) (mod_lt _ !zero_lt_succ)

definition minv : ∀ i : fin (succ n), fin (succ n)
| (mk iv ilt) := mk ((succ n - iv) mod succ n) (mod_lt _ !zero_lt_succ)

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

lemma madd_mk_mod {i j : nat} : madd (mk_mod n i) (mk_mod n j) = mk_mod n (i+j) :=
eq_of_veq begin esimp [madd, mk_mod], rewrite [ mod_add_mod, add_mod_mod ] end

lemma val_mod : ∀ i : fin (succ n), (val i) mod (succ n) = val i
| (mk iv ilt) := by esimp; rewrite [(mod_eq_of_lt ilt)]

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

lemma succ_max : fin.succ maxi = (@maxi (nat.succ n)) := rfl

lemma lift_succ.comm : lift_succ ∘ (@succ n) = succ ∘ lift_succ :=
funext take i, eq_of_veq (begin rewrite [↑lift_succ, -val_lift, *val_succ, -val_lift] end)

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
    have vk = vj+1, from
      eq.symm (succ_pred_of_pos HT),
    assert vj < n, from
      lt_of_succ_lt_succ (eq.subst `vk = vj+1` pk),
    have succ (mk vj `vj < n`) = mk vk pk, from
      val_inj (eq.symm `vk = vj+1`),
    eq.rec_on this (CS (mk vj `vj < n`)) },
  { show C (mk vk pk), from
    have vk = 0, from
      eq_zero_of_le_zero (le_of_not_gt HF),
    have zero n = mk vk pk, from
      val_inj (eq.symm this),
    eq.rec_on this CO }
end

definition succ_maxi_cases {C : fin (nat.succ n) → Type} :
  (Π j : fin n, C (lift_succ j)) → C maxi → (Π k : fin (nat.succ n), C k) :=
begin
  intros CL CM k,
  induction k with [vk, pk],
  induction (nat.decidable_lt vk n) with [HT, HF],
  { show C (mk vk pk), from
    have HL : lift_succ (mk vk HT) = mk vk pk, from
      val_inj rfl,
    eq.rec_on HL (CL (mk vk HT)) },
  { show C (mk vk pk), from
    have HMv : vk = n, from
      le.antisymm (le_of_lt_succ pk) (le_of_not_gt HF),
    have HM : maxi = mk vk pk, from
      val_inj (eq.symm HMv),
    eq.rec_on HM CM }
end

definition foldr {A B : Type} (m : A → B → B) (b : B) : ∀ {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (f (zero n)) (IH (λ i : fin n, f (succ i))))

definition foldl {A B : Type} (m : B → A → B) (b : B) : ∀ {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (IH (λ i : fin n, f (lift_succ i))) (f maxi))

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

section
open list
local postfix `+1`:100 := nat.succ

lemma dmap_map_lift {n : nat} : ∀ l : list nat, (∀ i, i ∈ l → i < n) → dmap (λ i, i < n +1) mk l = map lift_succ (dmap (λ i, i < n) mk l)
| []     := assume Plt, rfl
| (i::l) := assume Plt, begin
  rewrite [@dmap_cons_of_pos _ _ (λ i, i < n +1) _ _ _ (lt_succ_of_lt (Plt i !mem_cons)), @dmap_cons_of_pos _ _ (λ i, i < n) _ _ _ (Plt i !mem_cons), map_cons],
  congruence,
  apply dmap_map_lift,
  intro j Pjinl, apply Plt, apply mem_cons_of_mem, assumption end

lemma upto_succ (n : nat) : upto (n +1) = maxi :: map lift_succ (upto n) :=
begin
  rewrite [↑fin.upto, list.upto_succ, @dmap_cons_of_pos _ _ (λ i, i < n +1) _ _ _ (nat.self_lt_succ n)],
  congruence,
  apply dmap_map_lift, apply @list.lt_of_mem_upto
end

definition upto_step : ∀ {n : nat}, fin.upto (n +1) = (map succ (upto n))++[zero n]
| 0      := rfl
| (i +1) := begin rewrite [upto_succ i, map_cons, append_cons, succ_max, upto_succ, -lift_zero],
  congruence, rewrite [map_map, -lift_succ.comm, -map_map, -(map_singleton _ (zero i)), -map_append, -upto_step] end
end

open sum equiv decidable

definition fin_zero_equiv_empty : fin 0 ≃ empty :=
⦃ equiv,
  to_fun    := λ f : (fin 0), elim0 f,
  inv       := λ e : empty, empty.rec _ e,
  left_inv  := λ f : (fin 0), elim0 f,
  right_inv := λ e : empty, empty.rec _ e
⦄

definition fin_one_equiv_unit : fin 1 ≃ unit :=
⦃ equiv,
  to_fun := λ f : (fin 1), unit.star,
  inv    := λ u : unit,    fin.zero 0,
  left_inv := begin
    intro f, change mk 0 !zero_lt_succ = f, cases f with v h, congruence,
    have v +1 ≤ 1, from succ_le_of_lt h,
    have v ≤ 0, from le_of_succ_le_succ this,
    have v = 0, from eq_zero_of_le_zero this,
    subst v
  end,
  right_inv := begin
    intro u, cases u, reflexivity
  end
⦄

definition fin_sum_equiv (n m : nat) : (fin n + fin m) ≃ fin (n+m) :=
assert aux₁ : ∀ {v}, v < m → (v + n) < (n + m), from
  take v, suppose v < m, calc
     v + n < m + n   : add_lt_add_of_lt_of_le this !le.refl
       ... = n + m  : add.comm,
⦃ equiv,
  to_fun := λ s : sum (fin n) (fin m),
    match s with
    | sum.inl (mk v hlt) := mk v     (lt_add_of_lt_right hlt m)
    | sum.inr (mk v hlt) := mk (v+n) (aux₁ hlt)
    end,
  inv := λ f : fin (n + m),
    match f with
    | mk v hlt := if h : v < n then sum.inl (mk v h) else sum.inr (mk (v-n) (sub_lt_of_lt_add hlt (le_of_not_gt h)))
    end,
  left_inv := begin
    intro s, cases s with f₁ f₂,
    { cases f₁ with v hlt, esimp, rewrite [dif_pos hlt] },
    { cases f₂ with v hlt, esimp,
      have ¬ v + n < n, from
        suppose v + n < n,
        assert v < n - n, from lt_sub_of_add_lt this !le.refl,
        have v < 0, by rewrite [sub_self at this]; exact this,
        absurd this !not_lt_zero,
      rewrite [dif_neg this], congruence, congruence, rewrite [add_sub_cancel] }
  end,
  right_inv := begin
    intro f, cases f with v hlt, esimp, apply @by_cases (v < n),
    { intro h₁, rewrite [dif_pos h₁] },
    { intro h₁, rewrite [dif_neg h₁], esimp, congruence, rewrite [sub_add_cancel (le_of_not_gt h₁)] }
  end
⦄

definition fin_prod_equiv_of_pos (n m : nat) : n > 0 → (fin n × fin m) ≃ fin (n*m) :=
suppose n > 0,
assert aux₁ : ∀ {v₁ v₂}, v₁ < n → v₂ < m → v₁ + v₂ * n < n*m, from
  take v₁ v₂, assume h₁ h₂,
    have   nat.succ v₂ ≤ m, from succ_le_of_lt h₂,
    assert nat.succ v₂ * n ≤ m * n,       from mul_le_mul_right _ this,
    have   v₂ * n + n ≤ n * m,            by rewrite [-add_one at this, mul.right_distrib at this, one_mul at this, mul.comm m n at this]; exact this,
    assert v₁ + (v₂ * n + n) < n + n * m, from add_lt_add_of_lt_of_le h₁ this,
    have   v₁ + v₂ * n + n < n * m + n,   by rewrite [add.assoc, add.comm (n*m) n]; exact this,
    lt_of_add_lt_add_right this,
assert aux₂ : ∀ v, v mod n < n, from
  take v, mod_lt _ `n > 0`,
assert aux₃ : ∀ {v}, v < n * m → v div n < m, from
  take v, assume h, by rewrite mul.comm at h; exact div_lt_of_lt_mul h,
⦃ equiv,
  to_fun   := λ p : (fin n × fin m), match p with (mk v₁ hlt₁, mk v₂ hlt₂) := mk (v₁ + v₂ * n) (aux₁ hlt₁ hlt₂) end,
  inv      := λ f : fin (n*m), match f with (mk v hlt) := (mk (v mod n) (aux₂ v), mk (v div n) (aux₃ hlt)) end,
  left_inv := begin
    intro p, cases p with f₁ f₂, cases f₁ with v₁ hlt₁, cases f₂ with v₂ hlt₂, esimp,
    congruence,
      {congruence, rewrite [add_mul_mod_self, mod_eq_of_lt hlt₁] },
      {congruence, rewrite [add_mul_div_self `n > 0`, div_eq_zero_of_lt hlt₁, zero_add]}
  end,
  right_inv := begin
    intro f, cases f with v hlt, esimp, congruence,
    rewrite [add.comm, -eq_div_mul_add_mod]
  end
⦄

definition fin_prod_equiv : Π (n m : nat), (fin n × fin m) ≃ fin (n*m)
| 0     b := calc
  (fin 0 × fin b) ≃ (empty × fin b) : prod_congr fin_zero_equiv_empty !equiv.refl
          ...     ≃ empty           : prod_empty_left
          ...     ≃ fin 0           : fin_zero_equiv_empty
          ...     ≃ fin (0 * b)     : by rewrite zero_mul
| (a+1) b := fin_prod_equiv_of_pos (a+1) b dec_trivial

definition fin_two_equiv_bool : fin 2 ≃ bool :=
calc
  fin 2 ≃ fin (1 + 1)   : equiv.refl
   ...  ≃ fin 1 + fin 1 : fin_sum_equiv
   ...  ≃ unit + unit   : sum_congr fin_one_equiv_unit fin_one_equiv_unit
   ...  ≃ bool          : bool_equiv_unit_sum_unit

definition fin_sum_unit_equiv (n : nat) : fin n + unit ≃ fin (n+1) :=
calc
  fin n + unit ≃ fin n + fin 1 : sum_congr !equiv.refl (equiv.symm fin_one_equiv_unit)
          ...  ≃ fin (n+1)     : fin_sum_equiv
end fin
