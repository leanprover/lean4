----------------------------------------------------------------------------------------------------
--- Copyright (c) 2014 Floris van Doorn. All rights reserved.
--- Released under Apache 2.0 license as described in the file LICENSE.
--- Author: Floris van Doorn
----------------------------------------------------------------------------------------------------

import logic data.num tools.tactic struc.binary
using num tactic binary eq_proofs
using decidable (hiding induction_on rec_on)

-- TODO: this should go in tools, I think
namespace helper_tactics
  definition apply_refl := apply @refl
  tactic_hint apply_refl
end
using helper_tactics


-- data.nat.basic
-- ==============
--
-- Basic operations on the natural numbers.

-- Definition of the type
-- ----------------------

namespace nat
inductive nat : Type :=
| zero : nat
| succ : nat → nat

notation `ℕ` : max := nat


-- Coercion from num
-- -----------------

abbreviation plus (x y : ℕ) : ℕ :=
nat_rec x (λ n r, succ r) y

definition to_nat [coercion] [inline] (n : num) : ℕ :=
num_rec zero
    (λ n, pos_num_rec (succ zero) (λ n r, plus r (plus r (succ zero))) (λ n r, plus r r) n) n

theorem nat_rec_zero {P : ℕ → Type} (x : P 0) (f : ∀m, P m → P (succ m)) : nat_rec x f 0 = x

theorem nat_rec_succ {P : ℕ → Type} (x : P 0) (f : ∀m, P m → P (succ m)) (n : ℕ) :
  nat_rec x f (succ n) = f n (nat_rec x f n)

theorem induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : ∀ (n : ℕ) (IH : P n), P (succ n)) :
  P a :=
nat_rec H1 H2 a

definition rec_on {P : ℕ → Type} (n : ℕ) (H1 : P 0) (H2 : ∀m, P m → P (succ m)) : P n :=
nat_rec H1 H2 n


-- Successor and predecessor
-- -------------------------

theorem succ_ne_zero (n : ℕ) : succ n ≠ 0 :=
assume H : succ n = 0,
have H2 : true = false, from
  let f [inline] := (nat_rec false (fun a b, true)) in
    calc
      true = f (succ n) : _
       ... = f 0        : {H}
       ... = false      : _,
absurd H2 true_ne_false

-- add_rewrite succ_ne_zero

definition pred (n : ℕ) := nat_rec 0 (fun m x, m) n

theorem pred_zero : pred 0 = 0

theorem pred_succ (n : ℕ) : pred (succ n) = n

opaque_hint (hiding pred)

theorem zero_or_succ_pred (n : ℕ) : n = 0 ∨ n = succ (pred n) :=
induction_on n
  (or_inl (refl 0))
  (take m IH, or_inr
    (show succ m = succ (pred (succ m)), from congr2 succ (pred_succ m⁻¹)))

theorem zero_or_exists_succ (n : ℕ) : n = 0 ∨ ∃k, n = succ k :=
or_imp_or (zero_or_succ_pred n) (assume H, H)
    (assume H : n = succ (pred n), exists_intro (pred n) H)

theorem case {P : ℕ → Prop} (n : ℕ) (H1: P 0) (H2 : ∀m, P (succ m)) : P n :=
induction_on n H1 (take m IH, H2 m)

theorem discriminate {B : Prop} {n : ℕ} (H1: n = 0 → B) (H2 : ∀m, n = succ m → B) : B :=
or_elim (zero_or_succ_pred n)
  (take H3 : n = 0, H1 H3)
  (take H3 : n = succ (pred n), H2 (pred n) H3)

theorem succ_inj {n m : ℕ} (H : succ n = succ m) : n = m :=
calc
    n = pred (succ n) : pred_succ n⁻¹
  ... = pred (succ m) : {H}
  ... = m             : pred_succ m

theorem succ_ne_self (n : ℕ) : succ n ≠ n :=
induction_on n
  (take H : 1 = 0,
    have ne : 1 ≠ 0, from succ_ne_zero 0,
    absurd H ne)
  (take k IH H, IH (succ_inj H))

theorem decidable_eq [instance] (n m : ℕ) : decidable (n = m) :=
have general : ∀n, decidable (n = m), from
  rec_on m
    (take n,
      rec_on n
	(inl (refl 0))
	(λ m iH, inr (succ_ne_zero m)))
    (λ (m' : ℕ) (iH1 : ∀n, decidable (n = m')),
      take n, rec_on n
	(inr (ne_symm (succ_ne_zero m')))
	(λ (n' : ℕ) (iH2 : decidable (n' = succ m')),
	  have d1 : decidable (n' = m'), from iH1 n',
	  decidable.rec_on d1
	    (assume Heq : n' = m', inl (congr2 succ Heq))
	    (assume Hne : n' ≠ m',
	      have H1 : succ n' ≠ succ m', from
		assume Heq, absurd (succ_inj Heq) Hne,
	      inr H1))),
general n

theorem two_step_induction_on {P : ℕ → Prop} (a : ℕ) (H1 : P 0) (H2 : P 1)
    (H3 : ∀ (n : ℕ) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
have stronger : P a ∧ P (succ a), from
  induction_on a
    (and_intro H1 H2)
    (take k IH,
      have IH1 : P k, from and_elim_left IH,
      have IH2 : P (succ k), from and_elim_right IH,
	and_intro IH2 (H3 k IH1 IH2)),
  and_elim_left stronger

theorem sub_induction {P : ℕ → ℕ → Prop} (n m : ℕ) (H1 : ∀m, P 0 m)
   (H2 : ∀n, P (succ n) 0) (H3 : ∀n m, P n m → P (succ n) (succ m)) : P n m :=
have general : ∀m, P n m, from induction_on n
  (take m : ℕ, H1 m)
  (take k : ℕ,
    assume IH : ∀m, P k m,
    take m : ℕ,
    discriminate
      (assume Hm : m = 0,
	Hm⁻¹ ▸ (H2 k))
      (take l : ℕ,
	assume Hm : m = succ l,
	  Hm⁻¹ ▸ (H3 k l (IH l)))),
general m


-- Addition
-- --------

definition add (x y : ℕ) : ℕ := plus x y

infixl `+` : 65 := add

theorem add_zero_right (n : ℕ) : n + 0 = n

theorem add_succ_right (n m : ℕ) : n + succ m = succ (n + m)

opaque_hint (hiding add)

theorem add_zero_left (n : ℕ) : 0 + n = n :=
induction_on n
    (add_zero_right 0)
    (take m IH, show 0 + succ m = succ m, from
      calc
        0 + succ m = succ (0 + m) : add_succ_right _ _
            ... = succ m : {IH})

theorem add_succ_left (n m : ℕ) : (succ n) + m = succ (n + m) :=
induction_on m
    (calc
      succ n + 0 = succ n : add_zero_right (succ n)
        ... = succ (n + 0) : {symm (add_zero_right n)})
    (take k IH,
      calc
        succ n + succ k = succ (succ n + k) : add_succ_right _ _
          ... = succ (succ (n + k)) : {IH}
          ... = succ (n + succ k) : {symm (add_succ_right _ _)})

theorem add_comm (n m : ℕ) : n + m = m + n :=
induction_on m
    (trans (add_zero_right _) (symm (add_zero_left _)))
    (take k IH,
      calc
        n + succ k = succ (n+k) : add_succ_right _ _
          ... = succ (k + n) : {IH}
          ... = succ k + n : symm (add_succ_left _ _))

theorem add_move_succ (n m : ℕ) : succ n + m = n + succ m :=
calc
    succ n + m = succ (n + m) : add_succ_left n m
      ... = n +succ m : symm (add_succ_right n m)

theorem add_comm_succ (n m : ℕ) : n + succ m = m + succ n :=
calc
    n + succ m = succ n + m : symm (add_move_succ n m)
      ... = m + succ n : add_comm (succ n) m

theorem add_assoc (n m k : ℕ) : (n + m) + k = n + (m + k) :=
induction_on k
    (calc
      (n + m) + 0 = n + m : add_zero_right _
        ... = n + (m + 0) : {symm (add_zero_right m)})
    (take l IH,
      calc
        (n + m) + succ l = succ ((n + m) + l) : add_succ_right _ _
          ... = succ (n + (m + l)) : {IH}
          ... = n + succ (m + l) : symm (add_succ_right _ _)
          ... = n + (m + succ l) : {symm (add_succ_right _ _)})

theorem add_left_comm (n m k : ℕ) : n + (m + k) = m + (n + k) :=
left_comm add_comm add_assoc n m k

theorem add_right_comm (n m k : ℕ) : n + m + k = n + k + m :=
right_comm add_comm add_assoc n m k

-- add_rewrite add_zero_left add_zero_right
-- add_rewrite add_succ_left add_succ_right
-- add_rewrite add_comm add_assoc add_left_comm

-- ### cancelation

theorem add_cancel_left {n m k : ℕ} : n + m = n + k → m = k :=
induction_on n
  (take H : 0 + m = 0 + k,
    calc
      m = 0 + m : symm (add_zero_left m)
	... = 0 + k : H
	... = k : add_zero_left k)
  (take (n : ℕ) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k),
    have H2 : succ (n + m) = succ (n + k),
    from calc
      succ (n + m) = succ n + m : symm (add_succ_left n m)
	... = succ n + k : H
	... = succ (n + k) : add_succ_left n k,
    have H3 : n + m = n + k, from succ_inj H2,
    IH H3)

theorem add_cancel_right {n m k : ℕ} (H : n + m = k + m) : n = k :=
have H2 : m + n = m + k,
  from calc
    m + n = n + m : add_comm m n
    ... = k + m : H
    ... = m + k : add_comm k m,
  add_cancel_left H2

theorem add_eq_zero_left {n m : ℕ} : n + m = 0 → n = 0 :=
induction_on n
  (take (H : 0 + m = 0), refl 0)
  (take k IH,
    assume (H : succ k + m = 0),
    absurd_elim (succ k = 0)
      (show succ (k + m) = 0, from
	calc
	  succ (k + m) = succ k + m : symm (add_succ_left k m)
	    ... = 0 : H)
      (succ_ne_zero (k + m)))

theorem add_eq_zero_right {n m : ℕ} (H : n + m = 0) : m = 0 :=
add_eq_zero_left (trans (add_comm m n) H)

theorem add_eq_zero {n m : ℕ} (H : n + m = 0) : n = 0 ∧ m = 0 :=
and_intro (add_eq_zero_left H) (add_eq_zero_right H)

-- ### misc

theorem add_one (n : ℕ) : n + 1 = succ n :=
calc
  n + 1 = succ (n + 0) : add_succ_right _ _
    ... = succ n : {add_zero_right _}

theorem add_one_left (n : ℕ) : 1 + n = succ n :=
calc
  1 + n = succ (0 + n) : add_succ_left _ _
    ... = succ n : {add_zero_left _}

-- TODO: rename? remove?
theorem induction_plus_one {P : nat → Prop} (a : ℕ) (H1 : P 0)
    (H2 : ∀ (n : ℕ) (IH : P n), P (n + 1)) : P a :=
nat_rec H1 (take n IH, (add_one n) ▸ (H2 n IH)) a


-- Multiplication
-- --------------

definition mul (n m : ℕ) := nat_rec 0 (fun m x, x + n) m

infixl `*`:75 := mul

theorem mul_zero_right (n:ℕ) : n * 0 = 0

theorem mul_succ_right (n m:ℕ) : n * succ m = n * m + n

opaque_hint (hiding mul)

-- ### commutativity, distributivity, associativity, identity

theorem mul_zero_left (n:ℕ) : 0 * n = 0 :=
induction_on n
  (mul_zero_right 0)
  (take m IH,
    calc
      0 * succ m = 0 * m + 0 : mul_succ_right _ _
	... = 0 * m : add_zero_right _
	... = 0 : IH)

theorem mul_succ_left (n m:ℕ) : (succ n) * m = (n * m) + m :=
induction_on m
  (calc
    succ n * 0 = 0     : mul_zero_right _
      ... = n * 0      : symm (mul_zero_right _)
      ... = n * 0 + 0  : symm (add_zero_right _))
  (take k IH,
    calc
      succ n * succ k = (succ n * k) + succ n : mul_succ_right _ _
	  ... = (n * k) + k + succ n : { IH }
	  ... = (n * k) + (k + succ n) : add_assoc _ _ _
	  ... = (n * k) + (n + succ k) : {add_comm_succ _ _}
	  ... = (n * k) + n + succ k : symm (add_assoc _ _ _)
	  ... = (n * succ k) + succ k : {symm (mul_succ_right n k)})

theorem mul_comm (n m:ℕ) : n * m = m * n :=
induction_on m
  (trans (mul_zero_right _) (symm (mul_zero_left _)))
  (take k IH,
    calc
      n * succ k = n * k + n : mul_succ_right _ _
	... = k * n + n : {IH}
	... = (succ k) * n : symm (mul_succ_left _ _))

theorem mul_add_distr_left (n m k : ℕ) : (n + m) * k = n * k + m * k :=
induction_on k
  (calc
    (n + m) * 0 = 0 : mul_zero_right _
      ... = 0 + 0 : symm (add_zero_right _)
      ... = n * 0 + 0 : {symm (mul_zero_right _)}
      ... = n * 0 + m * 0 : {symm (mul_zero_right _)})
  (take l IH, calc
      (n + m) * succ l = (n + m) * l + (n + m) : mul_succ_right _ _
	... = n * l + m * l + (n + m) : {IH}
	... = n * l + m * l + n + m : symm (add_assoc _ _ _)
	... = n * l + n + m * l + m : {add_right_comm _ _ _}
	... = n * l + n + (m * l + m) : add_assoc _ _ _
	... = n * succ l + (m * l + m) : {symm (mul_succ_right _ _)}
	... = n * succ l + m * succ l : {symm (mul_succ_right _ _)})

theorem mul_add_distr_right (n m k : ℕ) : n * (m + k) = n * m + n * k :=
calc
  n * (m + k) = (m + k) * n : mul_comm _ _
    ... = m * n + k * n : mul_add_distr_left _ _ _
    ... = n * m + k * n : {mul_comm _ _}
    ... = n * m + n * k : {mul_comm _ _}

theorem mul_assoc (n m k:ℕ) : (n * m) * k = n * (m * k) :=
induction_on k
  (calc
    (n * m) * 0 = 0 : mul_zero_right _
      ... = n * 0 : symm (mul_zero_right _)
      ... = n * (m * 0) : {symm (mul_zero_right _)})
  (take l IH,
    calc
      (n * m) * succ l = (n * m) * l + n * m : mul_succ_right _ _
	... = n * (m * l) + n * m : {IH}
	... = n * (m * l + m) : symm (mul_add_distr_right _ _ _)
	... = n * (m * succ l) : {symm (mul_succ_right _ _)})

theorem mul_comm_left (n m k : ℕ) : n * (m * k) = m * (n * k) :=
left_comm mul_comm mul_assoc n m k

theorem mul_comm_right (n m k : ℕ) : n * m * k = n * k * m :=
right_comm mul_comm mul_assoc n m k

theorem mul_one_right (n : ℕ) : n * 1 = n :=
calc
  n * 1 = n * 0 + n : mul_succ_right n 0
    ... = 0 + n : {mul_zero_right n}
    ... = n : add_zero_left n

theorem mul_one_left (n : ℕ) : 1 * n = n :=
calc
  1 * n = n * 1 : mul_comm _ _
    ... = n : mul_one_right n

theorem mul_eq_zero {n m : ℕ} (H : n * m = 0) : n = 0 ∨ m = 0 :=
discriminate
  (take Hn : n = 0, or_intro_left _ Hn)
  (take (k : ℕ),
    assume (Hk : n = succ k),
    discriminate
      (take (Hm : m = 0), or_intro_right _ Hm)
      (take (l : ℕ),
	assume (Hl : m = succ l),
	have Heq : succ (k * succ l + l) = n * m, from
	  symm (calc
	    n * m = n * succ l : {Hl}
	      ... = succ k * succ l : {Hk}
	      ... = k * succ l + succ l : mul_succ_left _ _
	      ... = succ (k * succ l + l) : add_succ_right _ _),
	absurd_elim _  (trans Heq H) (succ_ne_zero _)))

---other inversion theorems appear below

-- add_rewrite mul_zero_left mul_zero_right mul_one_right mul_one_left
-- add_rewrite mul_succ_left mul_succ_right
-- add_rewrite mul_comm mul_assoc mul_left_comm
-- add_rewrite mul_distr_right mul_distr_left
