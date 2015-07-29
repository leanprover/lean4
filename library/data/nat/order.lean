/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad

The order relation on the natural numbers.
-/
import data.nat.basic algebra.ordered_ring
open eq.ops

namespace nat

/- lt and le -/

theorem le_of_lt_or_eq {m n : ℕ} (H : m < n ∨ m = n) : m ≤ n :=
le_of_eq_or_lt (or.swap H)

theorem lt_or_eq_of_le {m n : ℕ} (H : m ≤ n) : m < n ∨ m = n :=
or.swap (eq_or_lt_of_le H)

theorem le_iff_lt_or_eq (m n : ℕ) : m ≤ n ↔ m < n ∨ m = n :=
iff.intro lt_or_eq_of_le le_of_lt_or_eq

theorem lt_of_le_and_ne {m n : ℕ} (H1 : m ≤ n) : m ≠ n → m < n :=
or_resolve_right (eq_or_lt_of_le H1)

theorem lt_iff_le_and_ne (m n : ℕ) : m < n ↔ m ≤ n ∧ m ≠ n :=
iff.intro
  (take H, and.intro (le_of_lt H) (take H1, !lt.irrefl (H1 ▸ H)))
  (and.rec lt_of_le_and_ne)

theorem le_add_right (n k : ℕ) : n ≤ n + k :=
nat.rec !le.refl (λ k, le_succ_of_le) k

theorem le_add_left (n m : ℕ): n ≤ m + n :=
!add.comm ▸ !le_add_right

theorem le.intro {n m k : ℕ} (h : n + k = m) : n ≤ m :=
h ▸ !le_add_right

theorem le.elim {n m : ℕ} : n ≤ m → ∃k, n + k = m :=
le.rec (exists.intro 0 rfl) (λm h, Exists.rec
  (λ k H, exists.intro (succ k) (H ▸ rfl)))

theorem le.total {m n : ℕ} : m ≤ n ∨ n ≤ m :=
or.imp_left le_of_lt !lt_or_ge

/- addition -/

theorem add_le_add_left {n m : ℕ} (H : n ≤ m) (k : ℕ) : k + n ≤ k + m :=
obtain l Hl, from le.elim H, le.intro (Hl ▸ !add.assoc)

theorem add_le_add_right {n m : ℕ} (H : n ≤ m) (k : ℕ) : n + k ≤ m + k :=
!add.comm ▸ !add.comm ▸ add_le_add_left H k

theorem le_of_add_le_add_left {k n m : ℕ} (H : k + n ≤ k + m) : n ≤ m :=
obtain l Hl, from le.elim H, le.intro (add.cancel_left (!add.assoc⁻¹ ⬝ Hl))

theorem lt_of_add_lt_add_left {k n m : ℕ} (H : k + n < k + m) : n < m :=
let H' := le_of_lt H in
lt_of_le_and_ne (le_of_add_le_add_left H') (assume Heq, !lt.irrefl (Heq ▸ H))

theorem add_lt_add_left {n m : ℕ} (H : n < m) (k : ℕ) : k + n < k + m :=
lt_of_succ_le (!add_succ ▸ add_le_add_left (succ_le_of_lt H) k)

theorem add_lt_add_right {n m : ℕ} (H : n < m) (k : ℕ) : n + k < m + k :=
!add.comm ▸ !add.comm ▸ add_lt_add_left H k

theorem lt_add_of_pos_right {n k : ℕ} (H : k > 0) : n < n + k :=
!add_zero ▸ add_lt_add_left H n

/- multiplication -/

theorem mul_le_mul_left {n m : ℕ} (k : ℕ) (H : n ≤ m) : k * n ≤ k * m :=
obtain (l : ℕ) (Hl : n + l = m), from le.elim H,
have k * n + k * l = k * m, by rewrite [-mul.left_distrib, Hl],
le.intro this

theorem mul_le_mul_right {n m : ℕ} (k : ℕ) (H : n ≤ m) : n * k ≤ m * k :=
!mul.comm ▸ !mul.comm ▸ !mul_le_mul_left H

theorem mul_le_mul {n m k l : ℕ} (H1 : n ≤ k) (H2 : m ≤ l) : n * m ≤ k * l :=
le.trans (!mul_le_mul_right H1) (!mul_le_mul_left H2)

theorem mul_lt_mul_of_pos_left {n m k : ℕ} (H : n < m) (Hk : k > 0) : k * n < k * m :=
calc k * n < k * n + k : lt_add_of_pos_right Hk
      ...  ≤ k * m     : !mul_succ ▸ mul_le_mul_left k (succ_le_of_lt H)

theorem mul_lt_mul_of_pos_right {n m k : ℕ} (H : n < m) (Hk : k > 0) : n * k < m * k :=
!mul.comm ▸ !mul.comm ▸ mul_lt_mul_of_pos_left H Hk

/- min and max -/

-- Because these are defined in init/nat.lean, we cannot use the definitions in algebra.

definition max (a b : ℕ) : ℕ := if a < b then b else a
definition min (a b : ℕ) : ℕ := if a < b then a else b

theorem max_self [simp] (a : ℕ) : max a a = a :=
eq.rec_on !if_t_t rfl

theorem max_le {n m k : ℕ} (H₁ : n ≤ k) (H₂ : m ≤ k) : max n m ≤ k :=
if H : n < m then by rewrite [↑max, if_pos H]; apply H₂
else by rewrite [↑max, if_neg H]; apply H₁

theorem min_le_left (n m : ℕ) : min n m ≤ n :=
if H : n < m then by rewrite [↑min, if_pos H]
else assert H' : m ≤ n, from or_resolve_right !lt_or_ge H,
    by rewrite [↑min, if_neg H]; apply H'

theorem min_le_right (n m : ℕ) : min n m ≤ m :=
if H : n < m then by rewrite [↑min, if_pos H]; apply le_of_lt H
else assert H' : m ≤ n, from or_resolve_right !lt_or_ge H,
    by rewrite [↑min, if_neg H]

theorem le_min {n m k : ℕ} (H₁ : k ≤ n) (H₂ : k ≤ m) : k ≤ min n m :=
if H : n < m then by rewrite [↑min, if_pos H]; apply H₁
else by rewrite [↑min, if_neg H]; apply H₂

theorem eq_max_right {a b : ℕ} (H : a < b) : b = max a b :=
(if_pos H)⁻¹

theorem eq_max_left {a b : ℕ} (H : ¬ a < b) : a = max a b :=
(if_neg H)⁻¹

open decidable
theorem le_max_right (a b : ℕ) : b ≤ max a b :=
lt.by_cases
  (suppose a < b, (eq_max_right this) ▸ !le.refl)
  (suppose a = b, this ▸ !max_self⁻¹ ▸ !le.refl)
  (suppose b < a, (eq_max_left (lt.asymm this)) ▸ (le_of_lt this))

theorem le_max_left (a b : ℕ) : a ≤ max a b :=
if h : a < b then le_of_lt (eq.rec_on (eq_max_right h) h)
else (eq_max_left h) ▸ !le.refl

/- nat is an instance of a linearly ordered semiring and a lattice-/

section migrate_algebra
  open [classes] algebra
  local attribute nat.comm_semiring [instance]

  protected definition linear_ordered_semiring [reducible] :
    algebra.linear_ordered_semiring nat :=
  ⦃ algebra.linear_ordered_semiring, nat.comm_semiring,
    add_left_cancel            := @add.cancel_left,
    add_right_cancel           := @add.cancel_right,
    lt                         := lt,
    le                         := le,
    le_refl                    := le.refl,
    le_trans                   := @le.trans,
    le_antisymm                := @le.antisymm,
    le_total                   := @le.total,
    le_iff_lt_or_eq            := @le_iff_lt_or_eq,
    le_of_lt                   := @le_of_lt,
    lt_irrefl                  := @lt.irrefl,
    lt_of_lt_of_le             := @lt_of_lt_of_le,
    lt_of_le_of_lt             := @lt_of_le_of_lt,
    lt_of_add_lt_add_left      := @lt_of_add_lt_add_left,
    add_lt_add_left            := @add_lt_add_left,
    add_le_add_left            := @add_le_add_left,
    le_of_add_le_add_left      := @le_of_add_le_add_left,
    zero_lt_one                := zero_lt_succ 0,
    mul_le_mul_of_nonneg_left  := (take a b c H1 H2, mul_le_mul_left c H1),
    mul_le_mul_of_nonneg_right := (take a b c H1 H2, mul_le_mul_right c H1),
    mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right ⦄

  protected definition lattice [reducible] : algebra.lattice nat :=
  ⦃ algebra.lattice, nat.linear_ordered_semiring,
    min          := min,
    max          := max,
    min_le_left  := min_le_left,
    min_le_right := min_le_right,
    le_min       := @le_min,
    le_max_left  := le_max_left,
    le_max_right := le_max_right,
    max_le       := @max_le ⦄

  local attribute nat.linear_ordered_semiring [instance]
  local attribute nat.lattice [instance]

  migrate from algebra with nat
    replacing dvd → dvd, has_le.ge → ge, has_lt.gt → gt, min → min, max → max
    hiding add_pos_of_pos_of_nonneg,  add_pos_of_nonneg_of_pos,
      add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg, le_add_of_nonneg_of_le,
      le_add_of_le_of_nonneg, lt_add_of_nonneg_of_lt, lt_add_of_lt_of_nonneg,
      lt_of_mul_lt_mul_left, lt_of_mul_lt_mul_right, pos_of_mul_pos_left, pos_of_mul_pos_right,
      mul_lt_mul

  attribute le.trans ge.trans lt.trans gt.trans [trans]
  attribute lt_of_lt_of_le lt_of_le_of_lt gt_of_gt_of_ge gt_of_ge_of_gt [trans]

  theorem add_pos_left {a : ℕ} (H : 0 < a) (b : ℕ) : 0 < a + b :=
    @algebra.add_pos_of_pos_of_nonneg _ _ a b H !zero_le
  theorem add_pos_right {a : ℕ} (H : 0 < a) (b : ℕ) : 0 < b + a :=
    !add.comm ▸ add_pos_left H b
  theorem add_eq_zero_iff_eq_zero_and_eq_zero {a b : ℕ} :
    a + b = 0 ↔ a = 0 ∧ b = 0 :=
    @algebra.add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg _ _ a b !zero_le !zero_le
  theorem le_add_of_le_left {a b c : ℕ} (H : b ≤ c) : b ≤ a + c :=
    @algebra.le_add_of_nonneg_of_le _ _ a b c !zero_le H
  theorem le_add_of_le_right {a b c : ℕ} (H : b ≤ c) : b ≤ c + a :=
    @algebra.le_add_of_le_of_nonneg _ _ a b c H !zero_le
  theorem lt_add_of_lt_left {b c : ℕ} (H : b < c) (a : ℕ) : b < a + c :=
    @algebra.lt_add_of_nonneg_of_lt _ _ a b c !zero_le H
  theorem lt_add_of_lt_right {b c : ℕ} (H : b < c) (a : ℕ) : b < c + a :=
    @algebra.lt_add_of_lt_of_nonneg _ _ a b c H !zero_le
  theorem lt_of_mul_lt_mul_left {a b c : ℕ} (H : c * a < c * b) : a < b :=
    @algebra.lt_of_mul_lt_mul_left _ _ a b c H !zero_le
  theorem lt_of_mul_lt_mul_right {a b c : ℕ} (H : a * c < b * c) : a < b :=
    @algebra.lt_of_mul_lt_mul_right _ _ a b c H !zero_le
  theorem pos_of_mul_pos_left {a b : ℕ} (H : 0 < a * b) : 0 < b :=
    @algebra.pos_of_mul_pos_left _ _ a b H !zero_le
  theorem pos_of_mul_pos_right {a b : ℕ} (H : 0 < a * b) : 0 < a :=
    @algebra.pos_of_mul_pos_right _ _ a b H !zero_le
end migrate_algebra

theorem zero_le_one : 0 ≤ 1 := dec_trivial

/- properties specific to nat -/

theorem lt_intro {n m k : ℕ} (H : succ n + k = m) : n < m :=
lt_of_succ_le (le.intro H)

theorem lt_elim {n m : ℕ} (H : n < m) : ∃k, succ n + k = m :=
le.elim (succ_le_of_lt H)

theorem lt_add_succ (n m : ℕ) : n < n + succ m :=
lt_intro !succ_add_eq_succ_add

theorem eq_zero_of_le_zero {n : ℕ} (H : n ≤ 0) : n = 0 :=
obtain (k : ℕ) (Hk : n + k = 0), from le.elim H,
eq_zero_of_add_eq_zero_right Hk

/- succ and pred -/

theorem le_of_lt_succ {m n : nat} : m < succ n → m ≤ n :=
le_of_succ_le_succ

theorem lt_iff_succ_le (m n : nat) : m < n ↔ succ m ≤ n :=
iff.rfl

theorem lt_succ_iff_le (m n : nat) : m < succ n ↔ m ≤ n :=
iff.intro le_of_lt_succ lt_succ_of_le

theorem self_le_succ (n : ℕ) : n ≤ succ n :=
le.intro !add_one

theorem succ_le_or_eq_of_le {n m : ℕ} : n ≤ m → succ n ≤ m ∨ n = m :=
lt_or_eq_of_le

theorem pred_le_of_le_succ {n m : ℕ} : n ≤ succ m → pred n ≤ m :=
pred_le_pred

theorem succ_le_of_le_pred {n m : ℕ} : succ n ≤ m → n ≤ pred m :=
pred_le_pred

theorem pred_le_pred_of_le {n m : ℕ} : n ≤ m → pred n ≤ pred m :=
pred_le_pred

theorem pre_lt_of_lt {n m : ℕ} : n < m → pred n < m :=
lt_of_le_of_lt !pred_le

theorem lt_of_pred_lt_pred {n m : ℕ} (H : pred n < pred m) : n < m :=
lt_of_not_ge
  (suppose m ≤ n,
    not_lt_of_ge (pred_le_pred_of_le this) H)

theorem le_or_eq_succ_of_le_succ {n m : ℕ} (H : n ≤ succ m) : n ≤ m ∨ n = succ m :=
or.imp_left le_of_succ_le_succ (succ_le_or_eq_of_le H)

theorem le_pred_self (n : ℕ) : pred n ≤ n :=
!pred_le

theorem succ_pos (n : ℕ) : 0 < succ n :=
!zero_lt_succ

theorem succ_pred_of_pos {n : ℕ} (H : n > 0) : succ (pred n) = n :=
(or_resolve_right (eq_zero_or_eq_succ_pred n) (ne.symm (ne_of_lt H)))⁻¹

theorem exists_eq_succ_of_lt {n : ℕ} : Π {m : ℕ}, n < m → ∃k, m = succ k
| 0        H := absurd H !not_lt_zero
| (succ k) H := exists.intro k rfl

theorem lt_succ_self (n : ℕ) : n < succ n :=
lt.base n

lemma lt_succ_of_lt {i j : nat} : i < j → i < succ j :=
assume Plt, lt.trans Plt (self_lt_succ j)

/- other forms of induction -/
protected definition strong_rec_on {P : nat → Type} (n : ℕ) (H : ∀n, (∀m, m < n → P m) → P n) : P n :=
nat.rec (λm h, absurd h !not_lt_zero)
  (λn' (IH : ∀ {m : ℕ}, m < n' → P m) m l,
     or.by_cases (lt_or_eq_of_le (le_of_lt_succ l))
    IH (λ e, eq.rec (H n' @IH) e⁻¹)) (succ n) n !lt_succ_self

protected theorem strong_induction_on {P : nat → Prop} (n : ℕ) (H : ∀n, (∀m, m < n → P m) → P n) :
    P n :=
nat.strong_rec_on n H

protected theorem case_strong_induction_on {P : nat → Prop} (a : nat) (H0 : P 0)
  (Hind : ∀(n : nat), (∀m, m ≤ n → P m) → P (succ n)) : P a :=
nat.strong_induction_on a
  (take n,
   show (∀ m, m < n → P m) → P n, from
     nat.cases_on n
       (suppose (∀ m, m < 0 → P m), show P 0, from H0)
       (take n,
         suppose (∀ m, m < succ n → P m),
         show P (succ n), from
           Hind n (take m, assume H1 : m ≤ n, this _ (lt_succ_of_le H1))))

/- pos -/

theorem by_cases_zero_pos {P : ℕ → Prop} (y : ℕ) (H0 : P 0) (H1 : ∀ {y : nat}, y > 0 → P y) :
  P y :=
nat.cases_on y H0 (take y, H1 !succ_pos)

theorem eq_zero_or_pos (n : ℕ) : n = 0 ∨ n > 0 :=
or_of_or_of_imp_left
  (or.swap (lt_or_eq_of_le !zero_le))
  (suppose 0 = n, by subst n)

theorem pos_of_ne_zero {n : ℕ} (H : n ≠ 0) : n > 0 :=
or.elim !eq_zero_or_pos (take H2 : n = 0, by contradiction) (take H2 : n > 0, H2)

theorem ne_zero_of_pos {n : ℕ} (H : n > 0) : n ≠ 0 :=
ne.symm (ne_of_lt H)

theorem exists_eq_succ_of_pos {n : ℕ} (H : n > 0) : exists l, n = succ l :=
exists_eq_succ_of_lt H

theorem pos_of_dvd_of_pos {m n : ℕ} (H1 : m ∣ n) (H2 : n > 0) : m > 0 :=
pos_of_ne_zero
  (suppose m = 0,
   assert  n = 0, from eq_zero_of_zero_dvd (this ▸ H1),
   ne_of_lt H2 (by subst n))

/- multiplication -/

theorem mul_lt_mul_of_le_of_lt {n m k l : ℕ} (Hk : k > 0) (H1 : n ≤ k) (H2 : m < l) :
  n * m < k * l :=
lt_of_le_of_lt (mul_le_mul_right m H1) (mul_lt_mul_of_pos_left H2 Hk)

theorem mul_lt_mul_of_lt_of_le {n m k l : ℕ} (Hl : l > 0) (H1 : n < k) (H2 : m ≤ l) :
  n * m < k * l :=
lt_of_le_of_lt (mul_le_mul_left n H2) (mul_lt_mul_of_pos_right H1 Hl)

theorem mul_lt_mul_of_le_of_le {n m k l : ℕ} (H1 : n < k) (H2 : m < l) : n * m < k * l :=
have H3 : n * m ≤ k * m, from mul_le_mul_right m (le_of_lt H1),
have H4 : k * m < k * l, from mul_lt_mul_of_pos_left H2 (lt_of_le_of_lt !zero_le H1),
lt_of_le_of_lt H3 H4

theorem eq_of_mul_eq_mul_left {m k n : ℕ} (Hn : n > 0) (H : n * m = n * k) : m = k :=
have n * m ≤ n * k, by rewrite H,
have m ≤ k,         from le_of_mul_le_mul_left this Hn,
have n * k ≤ n * m, by rewrite H,
have k ≤ m,         from le_of_mul_le_mul_left this Hn,
le.antisymm `m ≤ k` this

theorem eq_of_mul_eq_mul_right {n m k : ℕ} (Hm : m > 0) (H : n * m = k * m) : n = k :=
eq_of_mul_eq_mul_left Hm (!mul.comm ▸ !mul.comm ▸ H)

theorem eq_zero_or_eq_of_mul_eq_mul_left {n m k : ℕ} (H : n * m = n * k) : n = 0 ∨ m = k :=
or_of_or_of_imp_right !eq_zero_or_pos
  (assume Hn : n > 0, eq_of_mul_eq_mul_left Hn H)

theorem eq_zero_or_eq_of_mul_eq_mul_right  {n m k : ℕ} (H : n * m = k * m) : m = 0 ∨ n = k :=
eq_zero_or_eq_of_mul_eq_mul_left (!mul.comm ▸ !mul.comm ▸ H)

theorem eq_one_of_mul_eq_one_right {n m : ℕ} (H : n * m = 1) : n = 1 :=
have H2 : n * m > 0, by rewrite H; apply succ_pos,
or.elim (le_or_gt n 1)
  (suppose n ≤ 1,
    have n > 0, from pos_of_mul_pos_right H2,
    show n = 1, from le.antisymm `n ≤ 1` (succ_le_of_lt this))
  (suppose n > 1,
    have m > 0, from pos_of_mul_pos_left H2,
    have n * m ≥ 2 * 1, from mul_le_mul (succ_le_of_lt `n > 1`) (succ_le_of_lt this),
    have 1 ≥ 2, from !mul_one ▸ H ▸ this,
    absurd !lt_succ_self (not_lt_of_ge this))

theorem eq_one_of_mul_eq_one_left {n m : ℕ} (H : n * m = 1) : m = 1 :=
eq_one_of_mul_eq_one_right (!mul.comm ▸ H)

theorem eq_one_of_mul_eq_self_left {n m : ℕ} (Hpos : n > 0) (H : m * n = n) : m = 1 :=
eq_of_mul_eq_mul_right Hpos (H ⬝ !one_mul⁻¹)

theorem eq_one_of_mul_eq_self_right {n m : ℕ} (Hpos : m > 0) (H : m * n = m) : n = 1 :=
eq_one_of_mul_eq_self_left Hpos (!mul.comm ▸ H)

theorem eq_one_of_dvd_one {n : ℕ} (H : n ∣ 1) : n = 1 :=
dvd.elim H
  (take m, suppose 1 = n * m,
   eq_one_of_mul_eq_one_right this⁻¹)

/- min and max -/
open decidable

theorem le_max_left_iff_true [simp] (a b : ℕ) : a ≤ max a b ↔ true :=
iff_true_intro (le_max_left a b)

theorem le_max_right_iff_true [simp] (a b : ℕ) : b ≤ max a b ↔ true :=
iff_true_intro (le_max_right a b)

theorem min_zero [simp] (a : ℕ) : min a 0 = 0 :=
by rewrite [min_eq_right !zero_le]

theorem zero_min [simp] (a : ℕ) : min 0 a = 0 :=
by rewrite [min_eq_left !zero_le]

theorem max_zero [simp] (a : ℕ) : max a 0 = a :=
by rewrite [max_eq_left !zero_le]

theorem zero_max [simp] (a : ℕ) : max 0 a = a :=
by rewrite [max_eq_right !zero_le]

theorem min_succ_succ [simp] (a b : ℕ) : min (succ a) (succ b) = succ (min a b) :=
by_cases
  (suppose a < b,   by unfold min; rewrite [if_pos this, if_pos (succ_lt_succ this)])
  (suppose ¬ a < b,
   assert h : ¬ succ a < succ b, from assume h, absurd (lt_of_succ_lt_succ h) this,
   by unfold min; rewrite [if_neg this, if_neg h])

theorem max_succ_succ [simp] (a b : ℕ) : max (succ a) (succ b) = succ (max a b) :=
by_cases
  (suppose a < b,   by unfold max; rewrite [if_pos this, if_pos (succ_lt_succ this)])
  (suppose ¬ a < b,
   assert ¬ succ a < succ b, from assume h, absurd (lt_of_succ_lt_succ h) this,
   by unfold max; rewrite [if_neg `¬ a < b`, if_neg `¬ succ a < succ b`])

theorem lt_min {a b c : ℕ} (H₁ : a < b) (H₂ : a < c) : a < min b c :=
decidable.by_cases
  (suppose b ≤ c, by rewrite (min_eq_left this); apply H₁)
  (suppose ¬ b ≤ c,
   assert c ≤ b, from le_of_lt (lt_of_not_ge this),
   by rewrite (min_eq_right this); apply H₂)

theorem max_lt {a b c : ℕ} (H₁ : a < c) (H₂ : b < c) : max a b < c :=
decidable.by_cases
  (suppose a ≤ b, by rewrite (max_eq_right this); apply H₂)
  (suppose ¬ a ≤ b,
   assert b ≤ a, from le_of_lt (lt_of_not_ge this),
   by rewrite (max_eq_left this); apply H₁)

theorem min_add_add_left (a b c : ℕ) : min (a + b) (a + c) = a + min b c :=
decidable.by_cases
  (suppose b ≤ c,
   assert a + b ≤ a + c, from add_le_add_left this _,
   by rewrite [min_eq_left `b ≤ c`, min_eq_left this])
  (suppose ¬ b ≤ c,
   assert c ≤ b,         from le_of_lt (lt_of_not_ge this),
   assert a + c ≤ a + b, from add_le_add_left this _,
   by rewrite [min_eq_right `c ≤ b`, min_eq_right this])

theorem min_add_add_right (a b c : ℕ) : min (a + c) (b + c) = min a b + c :=
by rewrite [add.comm a c, add.comm b c, add.comm _ c]; apply min_add_add_left

theorem max_add_add_left (a b c : ℕ) : max (a + b) (a + c) = a + max b c :=
decidable.by_cases
  (suppose b ≤ c,
   assert a + b ≤ a + c, from add_le_add_left this _,
   by rewrite [max_eq_right `b ≤ c`, max_eq_right this])
  (suppose ¬ b ≤ c,
   assert c ≤ b,         from le_of_lt (lt_of_not_ge this),
   assert a + c ≤ a + b, from add_le_add_left this _,
   by rewrite [max_eq_left `c ≤ b`, max_eq_left this])

theorem max_add_add_right (a b c : ℕ) : max (a + c) (b + c) = max a b + c :=
by rewrite [add.comm a c, add.comm b c, add.comm _ c]; apply max_add_add_left

theorem max_eq_right' {a b : ℕ} (H : a < b) : max a b = b :=
if_pos H

-- different versions will be defined in algebra
theorem max_eq_left' {a b : ℕ} (H : ¬ a < b) : max a b = a :=
if_neg H

lemma min_eq_left' {a b : nat} (H : a < b) : min a b = a :=
if_pos H

lemma min_eq_right' {a b : nat} (H : ¬ a < b) : min a b = b :=
if_neg H

/- greatest -/

section greatest
  variable (P : ℕ → Prop)
  variable [decP : ∀ n, decidable (P n)]
  include decP

  -- returns the largest i < n satisfying P, or n if there is none.
  definition greatest : ℕ → ℕ
  | 0        := 0
  | (succ n) := if P n then n else greatest n

  theorem greatest_of_lt {i n : ℕ} (ltin : i < n) (Hi : P i) : P (greatest P n) :=
  begin
    induction n with [m, ih],
      {exact absurd ltin !not_lt_zero},
      {cases (decidable.em (P m)) with [Psm, Pnsm],
        {rewrite [↑greatest, if_pos Psm]; exact Psm},
        {rewrite [↑greatest, if_neg Pnsm],
          have neim : i ≠ m, from assume H : i = m, absurd (H ▸ Hi) Pnsm,
          have ltim : i < m, from lt_of_le_of_ne (le_of_lt_succ ltin) neim,
          apply ih ltim}}
  end

  theorem le_greatest_of_lt {i n : ℕ} (ltin : i < n) (Hi : P i) : i ≤ greatest P n :=
  begin
    induction n with [m, ih],
      {exact absurd ltin !not_lt_zero},
      {cases (decidable.em (P m)) with [Psm, Pnsm],
        {rewrite [↑greatest, if_pos Psm], apply le_of_lt_succ ltin},
        {rewrite [↑greatest, if_neg Pnsm],
          have neim : i ≠ m, from assume H : i = m, absurd (H ▸ Hi) Pnsm,
          have ltim : i < m, from lt_of_le_of_ne (le_of_lt_succ ltin) neim,
          apply ih ltim}}
 end
end greatest

end nat
