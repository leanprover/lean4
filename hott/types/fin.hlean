/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura, Jakob von Raumer

Finite ordinal types.
-/
import types.list algebra.group function logic types.prod types.sum
open eq nat function list equiv is_trunc algebra sigma sum

structure fin (n : nat) := (val : nat) (is_lt : val < n)

definition less_than [reducible] := fin

namespace fin

attribute fin.val [coercion]

section def_equal
variable {n : nat}

definition sigma_char : fin n ≃ Σ (val : nat), val < n :=
begin
  fapply equiv.MK,
    intro i, cases i with i ilt, apply dpair i ilt,
    intro s, cases s with i ilt, apply fin.mk i ilt,
    intro s, cases s with i ilt, reflexivity,
    intro i, cases i with i ilt, reflexivity
end

definition is_hset_fin [instance] : is_hset (fin n) :=
begin
  apply is_trunc_equiv_closed, apply equiv.symm, apply sigma_char,
end

definition eq_of_veq : Π {i j : fin n}, (val i) = j → i = j :=
begin
  intro i j, cases i with i ilt, cases j with j jlt, esimp,
  intro p, induction p, apply ap (mk i), apply !is_hprop.elim
end

definition eq_of_veq_refl (i : fin n) : eq_of_veq (refl (val i)) = idp :=
!is_hprop.elim

definition veq_of_eq : Π {i j : fin n}, i = j → (val i) = j :=
by intro i j P; apply ap val; exact P


definition eq_iff_veq {i j : fin n} : (val i) = j ↔ i = j :=
pair eq_of_veq veq_of_eq

definition val_inj := @eq_of_veq n

end def_equal

section decidable
open decidable

protected definition has_decidable_eq [instance] (n : nat) :
  Π (i j : fin n), decidable (i = j) :=
begin
  intros i j, apply decidable_of_decidable_of_iff,
  apply nat.has_decidable_eq i j, apply eq_iff_veq,
end

end decidable

/-lemma dinj_lt (n : nat) : dinj (λ i, i < n) fin.mk :=
take a1 a2 Pa1 Pa2 Pmkeq, fin.no_confusion Pmkeq (λ Pe Pqe, Pe)

lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i := rfl

definition upto [reducible] (n : nat) : list (fin n) :=
dmap (λ i, i < n) fin.mk (list.upto n)

lemma nodup_upto (n : nat) : nodup (upto n) :=
dmap_nodup_of_dinj (dinj_lt n) (list.nodup_upto n)

lemma mem_upto (n : nat) : Π (i : fin n), i ∈ upto n :=
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

theorem pigeonhole {n m : nat} (Pmltn : m < n) : ¬Σ f : fin n → fin m, injective f :=
assume Pex, absurd Pmltn (not_lt_of_ge
  (calc
       n = card (fin n) : card_fin
     ... ≤ card (fin m) : card_le_of_inj (fin n) (fin m) Pex
     ... = m : card_fin))

end pigeonhole-/

protected definition zero [constructor] (n : nat) : fin (succ n) :=
mk 0 !zero_lt_succ

definition fin_has_zero [instance] [reducible] (n : nat) : has_zero (fin (succ n)) :=
has_zero.mk (fin.zero n)

definition val_zero (n : nat) : val (0 : fin (succ n)) = 0 := rfl

/-definition mk_mod [reducible] (n i : nat) : fin (succ n) :=
mk (i % (succ n)) (mod_lt _ !zero_lt_succ)-/

/-theorem mk_mod_zero_eq (n : nat) : mk_mod n 0 = 0 :=
rfl-/

variable {n : nat}

theorem val_lt : Π i : fin n, val i < n
| (mk v h) := h

lemma max_lt (i j : fin n) : max i j < n :=
max_lt (is_lt i) (is_lt j)

definition lift [constructor] : fin n → Π m : nat, fin (n + m)
| (mk v h) m := mk v (lt_add_of_lt_right h m)

definition lift_succ [constructor] (i : fin n) : fin (nat.succ n) :=
have r : fin (n+1), from lift i 1,
r

definition maxi [reducible] : fin (succ n) :=
mk n !lt_succ_self

definition val_lift : Π (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m := rfl

lemma mk_succ_ne_zero {i : nat} : Π {P}, mk (succ i) P ≠ (0 : fin (succ n)) :=
assume P Pe, absurd (veq_of_eq Pe) !succ_ne_zero

/-lemma mk_mod_eq {i : fin (succ n)} : i = mk_mod n i :=
eq_of_veq begin rewrite [↑mk_mod, mod_eq_of_lt !is_lt] end

lemma mk_mod_of_lt {i : nat} (Plt : i < succ n) : mk_mod n i = mk i Plt :=
begin esimp [mk_mod], congruence, exact mod_eq_of_lt Plt end
-/
section lift_lower

lemma lift_zero : lift_succ (0 : fin (succ n)) = (0 : fin (succ (succ n))) :=
by apply eq_of_veq; reflexivity

lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ maxi :=
begin
  intro hlt he, assert he' : maxi = i, apply he⁻¹, induction he', apply nat.lt_irrefl n hlt,
end

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

lemma lift_succ_inj [instance] : is_embedding (@lift_succ n) :=
begin
  apply is_embedding_of_is_injective, intro i j,
  induction i with iv ilt, induction j with jv jlt, intro Pmkeq,
  apply eq_of_veq, apply veq_of_eq Pmkeq
end

definition lt_of_inj_of_max (f : fin (succ n) → fin (succ n)) :
  is_embedding f → (f maxi = maxi) → Π i : fin (succ n), i < n → f i < n :=
assume Pinj Peq, take i, assume Pilt,
assert P1 : f i = f maxi → i = maxi, from assume Peq, is_injective_of_is_embedding Peq,
have f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max this

definition lift_fun : (fin n → fin n) → (fin (succ n) → fin (succ n)) :=
λ f i, dite (i = maxi) (λ Pe, maxi) (λ Pne, lift_succ (f (mk i (lt_max_of_ne_max Pne))))

definition lower_inj (f : fin (succ n) → fin (succ n)) (inj : is_embedding f) :
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
  rewrite [lift_fun_of_ne_max lift_succ_ne_max], do 2 congruence,
  apply eq_of_veq, esimp, rewrite -val_lift,
end

lemma lift_fun_of_inj {f : fin n → fin n} : is_embedding f → is_embedding (lift_fun f) :=
begin
  intro Pemb, apply is_embedding_of_is_injective, intro i j,
  assert Pdi : decidable (i = maxi), apply _,
  assert Pdj : decidable (j = maxi), apply _,
  cases Pdi with Pimax Pinmax,
    cases Pdj with Pjmax Pjnmax,
      substvars, intros, reflexivity,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pjnmax],
        intro Plmax, apply absurd Plmax⁻¹ lift_succ_ne_max,
    cases Pdj with Pjmax Pjnmax,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pinmax],
        intro Plmax, apply absurd Plmax lift_succ_ne_max,
      rewrite [lift_fun_of_ne_max Pinmax, lift_fun_of_ne_max Pjnmax],
        intro Peq, apply eq_of_veq,
        cases i with i ilt, cases j with j jlt, esimp at *,
        fapply veq_of_eq, apply is_injective_of_is_embedding,
        apply @is_injective_of_is_embedding _ _ lift_succ _ _ _ Peq,
end

lemma lift_fun_inj : is_embedding (@lift_fun n) :=
begin
  apply is_embedding_of_is_injective, intro f f' Peq, apply eq_of_homotopy, intro i,
  assert H : lift_fun f (lift_succ i) = lift_fun f' (lift_succ i), apply congr_fun Peq _,
  revert H, rewrite [*lift_fun_eq], apply is_injective_of_is_embedding,
end

lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)) :=
by rewrite [↑lower_inj]

end lift_lower
/-
section madd

definition madd (i j : fin (succ n)) : fin (succ n) :=
mk ((i + j) % (succ n)) (mod_lt _ !zero_lt_succ)

definition minv : Π i : fin (succ n), fin (succ n)
| (mk iv ilt) := mk ((succ n - iv) % succ n) (mod_lt _ !zero_lt_succ)

lemma val_madd : Π i j : fin (succ n), val (madd i j) = (i + j) % (succ n)
| (mk iv ilt) (mk jv jlt) := by esimp

lemma madd_inj : Π {i : fin (succ n)}, injective (madd i)
| (mk iv ilt) :=
take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (λ jv₁ jlt₁ jv₂ jlt₂, begin
  rewrite [↑madd, -eq_iff_veq],
  intro Peq, congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_mod_of_add_mod_eq_add_mod_left Peq
end))

lemma madd_mk_mod {i j : nat} : madd (mk_mod n i) (mk_mod n j) = mk_mod n (i+j) :=
eq_of_veq begin esimp [madd, mk_mod], rewrite [ mod_add_mod, add_mod_mod ] end

lemma val_mod : Π i : fin (succ n), (val i) % (succ n) = val i
| (mk iv ilt) := by esimp; rewrite [(mod_eq_of_lt ilt)]

lemma madd_comm (i j : fin (succ n)) : madd i j = madd j i :=
by apply eq_of_veq; rewrite [*val_madd, add.comm (val i)]

lemma zero_madd (i : fin (succ n)) : madd 0 i = i :=
have H : madd (fin.zero n) i = i,
  by apply eq_of_veq; rewrite [val_madd, ↑fin.zero, nat.zero_add, mod_eq_of_lt (is_lt i)],
H

lemma madd_zero (i : fin (succ n)) : madd i (fin.zero n) = i :=
!madd_comm ▸ zero_madd i

lemma madd_assoc (i j k : fin (succ n)) : madd (madd i j) k = madd i (madd j k) :=
by apply eq_of_veq; rewrite [*val_madd, mod_add_mod, add_mod_mod, add.assoc (val i)]

lemma madd_left_inv : Π i : fin (succ n), madd (minv i) i = fin.zero n
| (mk iv ilt) := eq_of_veq (by
  rewrite [val_madd, ↑minv, ↑fin.zero, mod_add_mod, nat.sub_add_cancel (le_of_lt ilt), mod_self])

definition madd_is_comm_group [instance] : add_comm_group (fin (succ n)) :=
add_comm_group.mk madd madd_assoc (fin.zero n) zero_madd madd_zero minv madd_left_inv madd_comm

end madd-/

definition pred [constructor] : fin n → fin n
| (mk v h) := mk (nat.pred v) (pre_lt_of_lt h)

lemma val_pred : Π (i : fin n), val (pred i) = nat.pred (val i)
| (mk v h) := rfl

lemma pred_zero : pred (fin.zero n) = fin.zero n :=
begin
  induction n, reflexivity, apply eq_of_veq, reflexivity,
end

definition mk_pred (i : nat) (h : succ i < succ n) : fin n :=
mk i (lt_of_succ_lt_succ h)

definition succ : fin n → fin (succ n)
| (mk v h) := mk (nat.succ v) (succ_lt_succ h)

lemma val_succ : Π (i : fin n), val (succ i) = nat.succ (val i)
| (mk v h) := rfl

lemma succ_max : fin.succ maxi = (@maxi (nat.succ n)) := rfl

lemma lift_succ.comm : lift_succ ∘ (@succ n) = succ ∘ lift_succ :=
eq_of_homotopy take i,
  eq_of_veq (begin rewrite [↑lift_succ, -val_lift, *val_succ, -val_lift] end)

definition elim0 {C : fin 0 → Type} : Π i : fin 0, C i
| (mk v h) := absurd h !not_lt_zero

definition zero_succ_cases {C : fin (nat.succ n) → Type} :
  C (fin.zero n) → (Π j : fin n, C (succ j)) → (Π k : fin (nat.succ n), C k) :=
begin
  intros CO CS k,
  induction k with [vk, pk],
  induction (nat.decidable_lt 0 vk) with [HT, HF],
  { show C (mk vk pk), from
    let vj := nat.pred vk in
    have vk = nat.succ vj, from
      inverse (succ_pred_of_pos HT),
    assert vj < n, from
      lt_of_succ_lt_succ (eq.subst `vk = nat.succ vj` pk),
    have succ (mk vj `vj < n`) = mk vk pk, by apply val_inj; apply (succ_pred_of_pos HT),
    eq.rec_on this (CS (mk vj `vj < n`)) },
  { show C (mk vk pk), from
    have vk = 0, from
      eq_zero_of_le_zero (le_of_not_gt HF),
    have fin.zero n = mk vk pk, from
      val_inj (inverse this),
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
      val_inj (inverse HMv),
    eq.rec_on HM CM }
end

open decidable

-- TODO there has to be a less painful way to do this
definition elim_succ_maxi_cases_lift_succ {C : fin (nat.succ n) → Type}
  {Cls : Π j : fin n, C (lift_succ j)} {Cm : C maxi} (i : fin n) :
  succ_maxi_cases Cls Cm (lift_succ i) = Cls i :=
begin
  esimp[succ_maxi_cases], cases i with i ilt, esimp,
  apply decidable.rec,
  { intro ilt', esimp[val_inj], apply concat,
    apply ap (λ x, eq.rec_on x _), esimp[eq_of_veq, rfl], reflexivity,
    assert H : ilt = ilt', apply is_hprop.elim, cases H,
    assert H' : is_hprop.elim (lt_add_of_lt_right ilt 1) (lt_add_of_lt_right ilt 1) = idp,
      apply is_hprop.elim,
    krewrite H' },
  { intro a, contradiction },
end

definition elim_succ_maxi_cases_maxi {C : fin (nat.succ n) → Type}
  {Cls : Π j : fin n, C (lift_succ j)} {Cm : C maxi} :
  succ_maxi_cases Cls Cm maxi = Cm :=
begin
  esimp[succ_maxi_cases, maxi],
  apply decidable.rec,
  { intro a, apply absurd a !nat.lt_irrefl },
  { intro a, esimp[val_inj], apply concat,
    assert H : (le.antisymm (le_of_lt_succ (lt_succ_self n)) (le_of_not_gt a))⁻¹ = idp,
      apply is_hprop.elim,
    apply ap _ H, krewrite eq_of_veq_refl },
end

definition foldr {A B : Type} (m : A → B → B) (b : B) : Π {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (f (fin.zero n)) (IH (λ i : fin n, f (succ i))))

definition foldl {A B : Type} (m : B → A → B) (b : B) : Π {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (IH (λ i : fin n, f (lift_succ i))) (f maxi))

/-theorem choice {C : fin n → Type} :
  (Π i : fin n, nonempty (C i)) → nonempty (Π i : fin n, C i) :=
begin
  revert C,
  induction n with [n, IH],
  { intros C H,
    apply nonempty.intro,
    exact elim0 },
  { intros C H,
    fapply nonempty.elim (H (fin.zero n)),
    intro CO,
    fapply nonempty.elim (IH (λ i, C (succ i)) (λ i, H (succ i))),
    intro CS,
    apply nonempty.intro,
    exact zero_succ_cases CO CS }
end-/

/-section
open list
local postfix `+1`:100 := nat.succ

lemma dmap_map_lift {n : nat} : Π l : list nat, (Π i, i ∈ l → i < n) → dmap (λ i, i < n +1) mk l = map lift_succ (dmap (λ i, i < n) mk l)
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

definition upto_step : Π {n : nat}, fin.upto (n +1) = (map succ (upto n))++[0]
| 0      := rfl
| (i +1) := begin rewrite [upto_succ i, map_cons, append_cons, succ_max, upto_succ, -lift_zero],
  congruence, rewrite [map_map, -lift_succ.comm, -map_map, -(map_singleton _ 0), -map_append, -upto_step] end
end-/

open sum equiv decidable

definition fin_zero_equiv_empty : fin 0 ≃ empty :=
begin
  fapply equiv.MK, rotate 1, do 2 (intro x; contradiction),
  rotate 1, do 2 (intro x; apply elim0 x)
end

definition is_contr_fin_one [instance] : is_contr (fin 1) :=
begin
  fapply is_contr.mk, exact 0,
  intro x, induction x with v vlt,
  apply eq_of_veq, rewrite val_zero,
  apply inverse, apply eq_zero_of_le_zero, apply le_of_succ_le_succ, exact vlt,
end

definition fin_sum_equiv (n m : nat) : (fin n + fin m) ≃ fin (n+m) :=
begin
  fapply equiv.MK,
  { intro s, induction s with l r,
    induction l with v vlt, apply mk v, apply lt_add_of_lt_right, exact vlt,
    induction r with v vlt, apply mk (v + n), rewrite {n + m}add.comm,
    apply add_lt_add_of_lt_of_le vlt, apply nat.le_refl },
  { intro f, induction f with v vlt,
    exact if h : v < n
          then sum.inl (mk v h)
          else sum.inr (mk (v-n) (nat.sub_lt_of_lt_add vlt (le_of_not_gt h))) },
  { intro f, cases f with v vlt, esimp, apply @by_cases (v < n),
    intro vltn, rewrite [dif_pos vltn], apply eq_of_veq, reflexivity,
    intro nvltn, rewrite [dif_neg nvltn], apply eq_of_veq, esimp,
    apply nat.sub_add_cancel, apply le_of_not_gt, apply nvltn },
  { intro s, cases s with f g,
    cases f with v vlt, rewrite [dif_pos vlt],
    cases g with v vlt, esimp, have ¬ v + n < n, from
      suppose v + n < n,
      assert v < n - n, from nat.lt_sub_of_add_lt this !le.refl,
      have v < 0, by rewrite [nat.sub_self at this]; exact this,
      absurd this !not_lt_zero,
    apply concat, apply dif_neg this, apply ap inr, apply eq_of_veq, esimp,
    apply nat.add_sub_cancel },
end

definition fin_succ_equiv (n : nat) : fin (n + 1) ≃ fin n + unit :=
begin
  fapply equiv.MK,
  { apply succ_maxi_cases, esimp, apply inl, apply inr unit.star },
  { intro d, cases d, apply lift_succ a, apply maxi },
  { intro d, cases d,
    cases a with a alt, esimp, apply elim_succ_maxi_cases_lift_succ,
    cases a, apply elim_succ_maxi_cases_maxi },
  { intro a, apply succ_maxi_cases, esimp,
    intro j, krewrite elim_succ_maxi_cases_lift_succ,
    krewrite elim_succ_maxi_cases_maxi },
end

open prod

definition fin_prod_equiv (n m : nat) : (fin n × fin m) ≃ fin (n*m) :=
begin
  induction n,
  { rewrite nat.zero_mul,
    calc fin 0 × fin m ≃ empty × fin m : fin_zero_equiv_empty
                   ... ≃ fin m × empty : prod_comm_equiv
                   ... ≃ empty : prod_empty_equiv
                   ... ≃ fin 0 : fin_zero_equiv_empty },
  { assert H : (a + 1) * m = a * m + m, rewrite [nat.right_distrib, one_mul],
    calc fin (a + 1) × fin m
         ≃ (fin a + unit) × fin m : prod.prod_equiv_prod_right !fin_succ_equiv
     ... ≃ (fin a × fin m) + (unit × fin m) : sum_prod_right_distrib
     ... ≃ (fin a × fin m) + (fin m × unit) : prod_comm_equiv
     ... ≃ fin (a * m) + (fin m × unit) : v_0
     ... ≃ fin (a * m) + fin m : prod_unit_equiv
     ... ≃ fin (a * m + m) : fin_sum_equiv
     ... ≃ fin ((a + 1) * m) : equiv_of_eq (ap fin H⁻¹) },
end

definition fin_two_equiv_bool : fin 2 ≃ bool :=
let H := equiv_unit_of_is_contr (fin 1) in
calc
  fin 2 ≃ fin (1 + 1)   : equiv.refl
   ...  ≃ fin 1 + fin 1 : fin_sum_equiv
   ...  ≃ unit + unit   : H
   ...  ≃ bool          : bool_equiv_unit_sum_unit

definition fin_sum_unit_equiv (n : nat) : fin n + unit ≃ fin (nat.succ n) :=
let H := equiv_unit_of_is_contr (fin 1) in
calc
  fin n + unit ≃ fin n + fin 1 : H
          ...  ≃ fin (nat.succ n)     : fin_sum_equiv

definition fin_sum_equiv_cancel {n : nat} {A B : Type} (H : (fin n) + A ≃ (fin n) + B) :
  A ≃ B :=
begin
  induction n with n IH,
  { calc A ≃ A + empty : sum_empty_equiv
       ... ≃ empty + A : sum_comm_equiv
       ... ≃ fin 0 + A : fin_zero_equiv_empty
       ... ≃ fin 0 + B : H
       ... ≃ empty + B : fin_zero_equiv_empty
       ... ≃ B + empty : sum_comm_equiv
       ... ≃ B : sum_empty_equiv },
  { apply IH, apply unit_sum_equiv_cancel,
    calc unit + (fin n + A) ≃ (unit + fin n) + A : sum_assoc_equiv
                        ... ≃ (fin n + unit) + A : sum_comm_equiv
                        ... ≃ fin (nat.succ n) + A : fin_sum_unit_equiv
                        ... ≃ fin (nat.succ n) + B : H
                        ... ≃ (fin n + unit) + B : fin_sum_unit_equiv
                        ... ≃ (unit + fin n) + B : sum_comm_equiv
                        ... ≃ unit + (fin n + B) : sum_assoc_equiv },
end


definition eq_of_fin_equiv {m n : nat} (H :fin m ≃ fin n) : m = n :=
begin
  revert n H, induction m with m IH IH,
  { intro n H, cases n, reflexivity, exfalso,
    apply to_fun fin_zero_equiv_empty, apply to_inv H, apply fin.zero },
  { intro n H, cases n with n, exfalso,
    apply to_fun fin_zero_equiv_empty, apply to_fun H, apply fin.zero,
    have unit + fin m ≃ unit + fin n, from
    calc unit + fin m ≃ fin m + unit : sum_comm_equiv
                  ... ≃ fin (nat.succ m) : fin_succ_equiv
                  ... ≃ fin (nat.succ n) : H
                  ... ≃ fin n + unit : fin_succ_equiv
                  ... ≃ unit + fin n : sum_comm_equiv,
    have fin m ≃ fin n, from unit_sum_equiv_cancel this,
    apply ap nat.succ, apply IH _ this },
end
end fin
