/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/

import data algebra.group algebra.group_power .finsubg .hom .perm

open function algebra finset
open eq.ops

namespace group

section cyclic
open nat fin

local attribute madd [reducible]

definition diff [reducible] (i j : nat) :=
if (i < j) then (j - i) else (i - j)

lemma diff_eq_dist {i j : nat} : diff i j = dist i j :=
#nat decidable.by_cases
  (λ Plt : i < j,
    by rewrite [if_pos Plt, ↑dist, sub_eq_zero_of_le (le_of_lt Plt), zero_add])
  (λ Pnlt : ¬ i < j,
    by rewrite [if_neg Pnlt, ↑dist, sub_eq_zero_of_le (le_of_not_gt Pnlt)])

lemma diff_eq_max_sub_min {i j : nat} : diff i j = (max i j) - min i j :=
decidable.by_cases
  (λ Plt : i < j, begin rewrite [↑max, ↑min, *(if_pos Plt)] end)
  (λ Pnlt : ¬ i < j, begin rewrite [↑max, ↑min, *(if_neg Pnlt)] end)

lemma diff_succ {i j : nat} : diff (succ i) (succ j) = diff i j :=
by rewrite [*diff_eq_dist, ↑dist, *succ_sub_succ]

lemma diff_add {i j k : nat} : diff (i + k) (j + k) = diff i j :=
by rewrite [*diff_eq_dist, dist_add_add_right]

lemma diff_le_max {i j : nat} : diff i j ≤ max i j :=
begin rewrite diff_eq_max_sub_min, apply sub_le end

lemma diff_gt_zero_of_ne {i j : nat} : i ≠ j → diff i j > 0 :=
assume Pne, decidable.by_cases
  (λ Plt : i < j, begin rewrite [if_pos Plt], apply sub_pos_of_lt Plt end)
  (λ Pnlt : ¬ i < j, begin
    rewrite [if_neg Pnlt], apply sub_pos_of_lt,
    apply lt_of_le_and_ne (nat.le_of_not_gt Pnlt) (ne.symm Pne) end)

variable {A : Type}

open list

variable [ambG : group A]
include ambG

lemma pow_mod {a : A} {n m : nat} : a ^ m = 1 → a ^ n = a ^ (n mod m) :=
assume Pid,
have Pm : a ^ (n div m * m) = 1, from calc
  a ^ (n div m * m) = a ^ (m * (n div m)) : {mul.comm (n div m) m}
                ... = (a ^ m) ^ (n div m) : !pow_mul
                ... = 1 ^ (n div m) : {Pid}
                ... = 1 : one_pow (n div m),
calc a ^ n = a ^ (n div m * m + n mod m) : {eq_div_mul_add_mod n m}
       ... = a ^ (n div m * m) * a ^ (n mod m) : !pow_add
       ... = 1 * a ^ (n mod m) : {Pm}
       ... = a ^ (n mod m) : !one_mul

lemma pow_sub_eq_one_of_pow_eq {a : A} {i j : nat} :
  a^i = a^j → a^(i - j) = 1 :=
assume Pe, or.elim (lt_or_ge i j)
  (assume Piltj, begin rewrite [sub_eq_zero_of_le (nat.le_of_lt Piltj)] end)
  (assume Pigej, begin rewrite [pow_sub a Pigej, Pe, mul.right_inv] end)

lemma pow_diff_eq_one_of_pow_eq {a : A} {i j : nat} :
  a^i = a^j → a^(diff i j) = 1 :=
assume Pe, decidable.by_cases
  (λ Plt : i < j, by rewrite [if_pos Plt]; exact pow_sub_eq_one_of_pow_eq (eq.symm Pe))
  (λ Pnlt : ¬ i < j, by rewrite [if_neg Pnlt]; exact pow_sub_eq_one_of_pow_eq Pe)

lemma pow_madd {a : A} {n : nat} {i j : fin (succ n)} :
  a^(succ n) = 1 → a^(val (i + j)) = a^i * a^j :=
assume Pe, calc
a^(val (i + j)) = a^((i + j) mod (succ n)) : rfl
            ... = a^(i + j) : pow_mod Pe
            ... = a^i * a^j : !pow_add

lemma mk_pow_mod {a : A} {n m : nat} : a ^ (succ m) = 1 → a ^ n = a ^ (mk_mod m n) :=
assume Pe, pow_mod Pe

variable [finA : fintype A]
include finA

open fintype

variable [deceqA : decidable_eq A]
include deceqA

lemma exists_pow_eq_one (a : A) : ∃ n, n < card A ∧ a ^ (succ n) = 1 :=
let f := (λ i : fin (succ (card A)), a ^ i) in
assert Pninj : ¬(injective f), from assume Pinj,
  absurd (card_le_of_inj _ _ (exists.intro f Pinj))
    (begin rewrite [card_fin], apply not_succ_le_self end),
obtain i₁ P₁, from exists_not_of_not_forall Pninj,
obtain i₂ P₂, from exists_not_of_not_forall P₁,
obtain Pfe Pne, from iff.elim_left not_implies_iff_and_not P₂,
assert Pvne : val i₁ ≠ val i₂, from assume Pveq, absurd (eq_of_veq Pveq) Pne,
exists.intro (pred (diff i₁ i₂)) (begin
  rewrite [succ_pred_of_pos (diff_gt_zero_of_ne Pvne)], apply and.intro,
    apply lt_of_succ_lt_succ,
    rewrite [succ_pred_of_pos (diff_gt_zero_of_ne Pvne)],
    apply nat.lt_of_le_of_lt diff_le_max (max_lt i₁ i₂),
    apply pow_diff_eq_one_of_pow_eq Pfe
  end)

-- Another possibility is to generate a list of powers and use find to get the first
-- unity.
-- The bound on bex is arbitrary as long as it is large enough (at least card A). Making
-- it larger simplifies some proofs, such as a ∈ cyc a.
definition cyc (a : A) : finset A := {x ∈ univ | bex (succ (card A)) (λ n, a ^ n = x)}

definition order (a : A) := card (cyc a)

definition pow_fin (a : A) (n : nat) (i : fin (order a)) := pow a (i + n)

definition cyc_pow_fin (a : A) (n : nat) : finset A := image (pow_fin a n) univ

lemma order_le_group_order {a : A} : order a ≤ card A :=
card_le_card_of_subset !subset_univ

lemma cyc_has_one (a : A) : 1 ∈ cyc a :=
begin
  apply mem_filter_of_mem !mem_univ,
  existsi 0, apply and.intro,
    apply zero_lt_succ,
    apply pow_zero
end

lemma order_pos (a : A) : 0 < order a :=
length_pos_of_mem (cyc_has_one a)

lemma cyc_mul_closed (a : A) : finset_mul_closed_on (cyc a) :=
take g h, assume Pgin Phin,
obtain n Plt Pe, from exists_pow_eq_one a,
obtain i Pilt Pig, from of_mem_filter Pgin,
obtain j Pjlt Pjh, from of_mem_filter Phin,
begin
  rewrite [-Pig, -Pjh, -pow_add, pow_mod Pe],
  apply mem_filter_of_mem !mem_univ,
  existsi ((i + j) mod (succ n)), apply and.intro,
    apply nat.lt.trans (mod_lt (i+j) !zero_lt_succ) (succ_lt_succ Plt),
    apply rfl
end

lemma cyc_has_inv (a : A) : finset_has_inv (cyc a) :=
take g, assume Pgin,
obtain n Plt Pe, from exists_pow_eq_one a,
obtain i Pilt Pig, from of_mem_filter Pgin,
let ni := -(mk_mod n i) in
assert Pinv : g*a^ni = 1, by
  rewrite [-Pig, mk_pow_mod Pe, -(pow_madd Pe), add.right_inv],
begin
  rewrite [inv_eq_of_mul_eq_one Pinv],
  apply mem_filter_of_mem !mem_univ,
  existsi ni, apply and.intro,
    apply nat.lt.trans (is_lt ni) (succ_lt_succ Plt),
    apply rfl
end

lemma self_mem_cyc (a : A) : a ∈ cyc a :=
mem_filter_of_mem !mem_univ
  (exists.intro (1 : nat) (and.intro (succ_lt_succ card_pos) !pow_one))

lemma mem_cyc (a : A) : ∀ {n : nat}, a^n ∈ cyc a
| 0        := cyc_has_one a
| (succ n) :=
  begin rewrite pow_succ, apply cyc_mul_closed a, exact mem_cyc, apply self_mem_cyc end

lemma order_le {a : A} {n : nat} : a^(succ n) = 1 → order a ≤ succ n :=
assume Pe, let s := image (pow a) (upto (succ n)) in
assert Psub: cyc a ⊆ s, from subset_of_forall
  (take g, assume Pgin, obtain i Pilt Pig, from of_mem_filter Pgin, begin
  rewrite [-Pig, pow_mod Pe],
  apply mem_image,
    apply mem_upto_of_lt (mod_lt i !zero_lt_succ),
    exact rfl end),
#nat calc order a ≤ card s : card_le_card_of_subset Psub
              ... ≤ card (upto (succ n)) : !card_image_le
              ... = succ n : card_upto (succ n)

lemma pow_ne_of_lt_order {a : A} {n : nat} : succ n < order a → a^(succ n) ≠ 1 :=
assume Plt, not_imp_not_of_imp order_le (nat.not_le_of_gt Plt)

lemma eq_zero_of_pow_eq_one {a : A} : ∀ {n : nat}, a^n = 1 → n < order a → n = 0
| 0        := assume Pe Plt, rfl
| (succ n) := assume Pe Plt, absurd Pe (pow_ne_of_lt_order Plt)

lemma pow_fin_inj (a : A) (n : nat) : injective (pow_fin a n) :=
take i j, assume Peq : a^(i + n) = a^(j + n),
have Pde : a^(diff i j) = 1, from diff_add ▸ pow_diff_eq_one_of_pow_eq Peq,
have Pdz : diff i j = 0, from eq_zero_of_pow_eq_one Pde
  (nat.lt_of_le_of_lt diff_le_max (max_lt i j)),
eq_of_veq (eq_of_dist_eq_zero (diff_eq_dist ▸ Pdz))

lemma cyc_eq_cyc (a : A) (n : nat) : cyc_pow_fin a n = cyc a :=
assert Psub : cyc_pow_fin a n ⊆ cyc a, from subset_of_forall
  (take g, assume Pgin,
  obtain i Pin Pig, from exists_of_mem_image Pgin, by rewrite [-Pig]; apply mem_cyc),
eq_of_card_eq_of_subset (begin apply eq.trans,
    apply card_image_eq_of_inj_on,
      rewrite [to_set_univ, -set.injective_iff_inj_on_univ], exact pow_fin_inj a n,
    rewrite [card_fin] end) Psub

lemma pow_order (a : A) : a^(order a) = 1 :=
obtain i Pin Pone, from exists_of_mem_image (eq.symm (cyc_eq_cyc a 1) ▸ cyc_has_one a),
or.elim (eq_or_lt_of_le (succ_le_of_lt (is_lt i)))
  (assume P, P ▸ Pone) (assume P, absurd Pone (pow_ne_of_lt_order P))

lemma eq_one_of_order_eq_one {a : A} : order a = 1 → a = 1 :=
assume Porder,
calc a = a^1 : eq.symm (pow_one a)
   ... = a^(order a) : Porder
   ... = 1 : pow_order

lemma order_of_min_pow {a : A} {n : nat}
  (Pone : a^(succ n) = 1) (Pmin : ∀ i, i < n → a^(succ i) ≠ 1) : order a = succ n :=
or.elim (eq_or_lt_of_le (order_le Pone)) (λ P, P)
  (λ P : order a < succ n, begin
  assert Pn : a^(order a) ≠ 1,
    rewrite [-(succ_pred_of_pos (order_pos a))],
    apply Pmin, apply nat.lt_of_succ_lt_succ,
    rewrite [succ_pred_of_pos !order_pos], assumption,
  exact absurd (pow_order a) Pn end)

lemma order_dvd_of_pow_eq_one {a : A} {n : nat} (Pone : a^n = 1) : order a ∣ n :=
assert Pe : a^(n mod order a) = 1, from
  begin
    revert Pone,
    rewrite [eq_div_mul_add_mod n (order a) at {1}, pow_add, mul.comm _ (order a), pow_mul, pow_order, one_pow, one_mul],
    intros, assumption
  end,
dvd_of_mod_eq_zero (eq_zero_of_pow_eq_one Pe (mod_lt n !order_pos))

definition cyc_is_finsubg [instance] (a : A) : is_finsubg (cyc a) :=
is_finsubg.mk (cyc_has_one a) (cyc_mul_closed a) (cyc_has_inv a)

lemma order_dvd_group_order (a : A) : order a ∣ card A :=
dvd.intro (eq.symm (!mul.comm ▸ lagrange_theorem (subset_univ (cyc a))))

definition pow_fin' (a : A) (i : fin (succ (pred (order a)))) := pow a i

local attribute group_of_add_group [instance]

lemma pow_fin_hom (a : A) : homomorphic (pow_fin' a) :=
take i j,
begin
  rewrite [↑pow_fin'],
  apply pow_madd,
  rewrite [succ_pred_of_pos !order_pos],
  exact pow_order a
end

definition pow_fin_is_iso (a : A) : is_iso_class (pow_fin' a) :=
is_iso_class.mk (pow_fin_hom a)
  (begin rewrite [↑pow_fin', succ_pred_of_pos !order_pos], exact pow_fin_inj a 0 end)

end cyclic

section rot
open nat list
open fin fintype list

section
local attribute group_of_add_group [instance]
local infix ^ := algebra.pow
lemma pow_eq_mul {n : nat} {i : fin (succ n)} : ∀ {k : nat}, i^k = mk_mod n (i*k)
| 0        := by rewrite [pow_zero]
| (succ k) := begin
  assert Psucc : i^(succ k) = madd (i^k) i, apply pow_succ,
  rewrite [Psucc, pow_eq_mul],
  apply eq_of_veq,
  rewrite [mul_succ, val_madd, ↑mk_mod, mod_add_mod]
  end

end

definition rotl : ∀ {n : nat} m : nat, fin n → fin n
| 0        := take m i, elim0 i
| (succ n) := take m, madd (mk_mod n (n*m))

definition rotr : ∀ {n : nat} m : nat, fin n → fin n
| (0:nat)      := take m i, elim0 i
| (nat.succ n) := take m, madd (-(mk_mod n (n*m)))

lemma rotl_succ' {n m : nat} : rotl m = madd (mk_mod n (n*m)) := rfl

lemma rotl_zero : ∀ {n : nat}, @rotl n 0 = id
| 0        := funext take i, elim0 i
| (succ n) := funext take i, zero_add i

lemma rotl_id : ∀ {n : nat}, @rotl n n = id
| 0        := funext take i, elim0 i
| (succ n) :=
  assert P : mk_mod n (n * succ n) = mk_mod n 0,
    from eq_of_veq !mul_mod_left,
  begin rewrite [rotl_succ', P], apply rotl_zero end

lemma rotl_to_zero {n i : nat} : rotl i (mk_mod n i) = zero n :=
eq_of_veq begin rewrite [↑rotl, val_madd], esimp [mk_mod], rewrite [ mod_add_mod, add_mod_mod, -succ_mul, mul_mod_right] end

lemma rotl_compose : ∀ {n : nat} {j k : nat}, (@rotl n j) ∘ (rotl k) = rotl (j + k)
| 0        := take j k, funext take i, elim0 i
| (succ n) :=  take j k, funext take i, eq.symm begin
  rewrite [*rotl_succ', mul.left_distrib, -(@madd_mk_mod n (n*j)), madd_assoc],
  end

lemma rotr_rotl : ∀ {n : nat} (m : nat) {i : fin n}, rotr m (rotl m i) = i
| 0            := take m i, elim0 i
| (nat.succ n) := take m i, calc (-(mk_mod n (n*m))) + ((mk_mod n (n*m)) + i) = i : by rewrite neg_add_cancel_left

lemma rotl_rotr : ∀ {n : nat} (m : nat), (@rotl n m) ∘ (rotr m) = id
| 0            := take m, funext take i, elim0 i
| (nat.succ n) := take m, funext take i, calc (mk_mod n (n*m)) + (-(mk_mod n (n*m)) + i) = i : add_neg_cancel_left

lemma rotl_succ {n : nat} : (rotl 1) ∘ (@succ n) = lift_succ :=
funext (take i, eq_of_veq (begin rewrite [↑compose, ↑rotl, ↑madd, mul_one n, ↑mk_mod, mod_add_mod, ↑lift_succ, val_succ, -succ_add_eq_succ_add, add_mod_self_left, mod_eq_of_lt (lt.trans (is_lt i) !lt_succ_self), -val_lift] end))

definition list.rotl {A : Type} : ∀ l : list A, list A
| []     := []
| (a::l) := l++[a]

lemma rotl_cons {A : Type} {a : A} {l} : list.rotl (a::l) = l++[a] := rfl

lemma rotl_map {A B : Type} {f : A → B} : ∀ {l : list A}, list.rotl (map f l) = map f (list.rotl l)
| []     := rfl
| (a::l) := begin rewrite [map_cons, *rotl_cons, map_append] end

lemma rotl_eq_rotl : ∀ {n : nat}, map (rotl 1) (upto n) = list.rotl (upto n)
| 0        := rfl
| (succ n) := begin
  rewrite [upto_step at {1}, upto_succ, rotl_cons, map_append],
  congruence,
    rewrite [map_map], congruence, exact rotl_succ,
    rewrite [map_singleton], congruence, rewrite [↑rotl, mul_one n, ↑mk_mod, ↑zero, ↑maxi, ↑madd],
      congruence, rewrite [ mod_add_mod, nat.add_zero, mod_eq_of_lt !lt_succ_self ]
  end

definition seq [reducible] (A : Type) (n : nat) := fin n → A

variable {A : Type}

definition rotl_fun {n : nat} (m : nat) (f : seq A n) : seq A n := f ∘ (rotl m)
definition rotr_fun {n : nat} (m : nat) (f : seq A n) : seq A n := f ∘ (rotr m)

lemma rotl_seq_zero {n : nat} : rotl_fun 0 = @id (seq A n) :=
funext take f, begin rewrite [↑rotl_fun, rotl_zero] end

lemma rotl_seq_ne_id : ∀ {n : nat}, (∃ a b : A, a ≠ b) → ∀ i, i < n → rotl_fun (succ i) ≠ (@id (seq A (succ n)))
| 0        := assume Pex, take i, assume Piltn, absurd Piltn !not_lt_zero
| (succ n) := assume Pex, obtain a b Pne, from Pex, take i, assume Pilt,
  let f := (λ j : fin (succ (succ n)), if j = zero (succ n) then a else b),
      fi := mk_mod (succ n) (succ i) in
  have Pfne : rotl_fun (succ i) f fi ≠ f fi,
    from begin rewrite [↑rotl_fun, rotl_to_zero, mk_mod_of_lt (succ_lt_succ Pilt), if_pos rfl, if_neg mk_succ_ne_zero], assumption end,
  have P : rotl_fun (succ i) f ≠ f, from
    assume Peq, absurd (congr_fun Peq fi) Pfne,
  assume Peq, absurd (congr_fun Peq f) P

lemma rotr_rotl_fun {n : nat} (m : nat) (f : seq A n) : rotr_fun m (rotl_fun m f) = f :=
calc f ∘ (rotl m) ∘ (rotr m) = f ∘ ((rotl m) ∘ (rotr m)) : compose.assoc
                         ... = f ∘ id : {rotl_rotr m}

lemma rotl_fun_inj {n : nat} {m : nat} : @injective (seq A n) (seq A n) (rotl_fun m) :=
injective_of_has_left_inverse (exists.intro (rotr_fun m) (rotr_rotl_fun m))

lemma seq_rotl_eq_list_rotl {n : nat} (f : seq A n) :
  fun_to_list (rotl_fun 1 f) = list.rotl (fun_to_list f) :=
begin
  rewrite [↑fun_to_list, ↑rotl_fun, -map_map, rotl_map],
  congruence, exact rotl_eq_rotl
end

end rot

section rotg
open nat fin fintype

definition rotl_perm [reducible] (A : Type) [finA : fintype A] [deceqA : decidable_eq A] (n : nat) (m : nat) : perm (seq A n) :=
perm.mk (rotl_fun m) rotl_fun_inj

variable {A : Type}
variable [finA : fintype A]
include finA
variable [deceqA : decidable_eq A]
include deceqA

variable {n : nat}

lemma rotl_perm_mul {i j : nat} : (rotl_perm A n i) * (rotl_perm A n j) = rotl_perm A n (j+i) :=
eq_of_feq (funext take f, calc
  f ∘ (rotl j) ∘ (rotl i) = f ∘ ((rotl j) ∘ (rotl i)) : compose.assoc
                      ... = f ∘ (rotl (j+i)) : rotl_compose)

lemma rotl_perm_pow_eq : ∀ {i : nat}, (rotl_perm A n 1) ^ i = rotl_perm A n i
| 0 := begin rewrite [pow_zero, ↑rotl_perm, perm_one, -eq_iff_feq], esimp, rewrite rotl_seq_zero  end
| (succ i) := begin rewrite [pow_succ, rotl_perm_pow_eq, rotl_perm_mul, one_add] end

lemma rotl_perm_pow_eq_one : (rotl_perm A n 1) ^ n = 1 :=
eq.trans rotl_perm_pow_eq (eq_of_feq begin esimp [rotl_perm], rewrite [↑rotl_fun, rotl_id] end)

lemma rotl_perm_mod {i : nat} : rotl_perm A n i = rotl_perm A n (i mod n) :=
calc rotl_perm A n i = (rotl_perm A n 1) ^ i : rotl_perm_pow_eq
                 ... = (rotl_perm A n 1) ^ (i mod n) : pow_mod rotl_perm_pow_eq_one
                 ... = rotl_perm A n (i mod n) : rotl_perm_pow_eq

-- needs A to have at least two elements!
lemma rotl_perm_pow_ne_one (Pex : ∃ a b : A, a ≠ b) : ∀ i, i < n → (rotl_perm A (succ n) 1)^(succ i) ≠ 1 :=
take i, assume Piltn, begin
  intro P, revert P, rewrite [rotl_perm_pow_eq, -eq_iff_feq, perm_one, *perm.f_mk],
  intro P, exact absurd P (rotl_seq_ne_id Pex i Piltn)
end

lemma rotl_perm_order (Pex : ∃ a b : A, a ≠ b) : order (rotl_perm A (succ n) 1) = (succ n) :=
order_of_min_pow rotl_perm_pow_eq_one (rotl_perm_pow_ne_one Pex)

end rotg
end group
