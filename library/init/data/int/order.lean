/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
prelude
import init.data.int.basic init.data.ordering.basic

namespace int

private def nonneg (a : ℤ) : Prop := int.cases_on a (assume n, true) (assume n, false)

protected def le (a b : ℤ) : Prop := nonneg (b - a)

instance : has_le int := ⟨int.le⟩

protected def lt (a b : ℤ) : Prop := (a + 1) ≤ b

instance : has_lt int := ⟨int.lt⟩

private def decidable_nonneg (a : ℤ) : decidable (nonneg a) :=
int.cases_on a (assume a, decidable.true) (assume a, decidable.false)

instance decidable_le (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

instance decidable_lt (a b : ℤ) : decidable (a < b) := decidable_nonneg _

lemma lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl _

private lemma nonneg.elim {a : ℤ} : nonneg a → ∃ n : ℕ, a = n :=
int.cases_on a (assume n H, exists.intro n rfl) (assume n', false.elim)

private lemma nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (assume n, or.inl trivial) (assume n, or.inr trivial)

lemma le.intro_sub {a b : ℤ} {n : ℕ} (h : b - a = n) : a ≤ b :=
show nonneg (b - a), by rw h; trivial

lemma le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
le.intro_sub (by rw [← h]; simp)

lemma le.dest_sub {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, b - a = n := nonneg.elim h

lemma le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
match (le.dest_sub h) with
| ⟨n, h₁⟩ := exists.intro n begin rw [← h₁, add_comm], simp end
end

lemma le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
exists.elim (le.dest h) h'

protected lemma le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or.imp_right
  (assume H : nonneg (-(b - a)),
   have -(b - a) = a - b, by simp,
   show nonneg (a - b), from this ▸ H)
  (nonneg_or_nonneg_neg (b - a))

lemma coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
match nat.le.dest h with
| ⟨k, (hk : m + k = n)⟩ := le.intro (begin rw [← hk], reflexivity end)
end

lemma le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
le.elim h (assume k, assume hk : ↑m + ↑k = ↑n,
  have m + k = n, from int.coe_nat_inj ((int.coe_nat_add m k).trans hk),
  nat.le.intro this)

lemma coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

lemma coe_zero_le (n : ℕ) : 0 ≤ (↑n : ℤ) :=
coe_nat_le_coe_nat_of_le n.zero_le

lemma eq_coe_of_zero_le {a : ℤ} (h : 0 ≤ a) : ∃ n : ℕ, a = n :=
by have t := le.dest_sub h; simp at t; exact t

lemma eq_succ_of_zero_lt {a : ℤ} (h : 0 < a) : ∃ n : ℕ, a = n.succ :=
let ⟨n, (h : ↑(1+n) = a)⟩ := le.dest h in
⟨n, by rw add_comm at h; exact h.symm⟩

lemma lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(nat.succ n) :=
le.intro (show a + 1 + n = a + nat.succ n, begin simp [int.coe_nat_eq], reflexivity end)

lemma lt.intro {a b : ℤ} {n : ℕ} (h : a + nat.succ n = b) : a < b :=
h ▸ lt_add_succ a n

lemma lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(nat.succ n) = b :=
le.elim h (assume n, assume hn : a + 1 + n = b,
    exists.intro n begin rw [← hn, add_assoc, add_comm (1 : int)], reflexivity end)

lemma lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(nat.succ n) = b → P) : P :=
exists.elim (lt.dest h) h'

lemma coe_nat_lt_coe_nat_iff (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m :=
begin rw [lt_iff_add_one_le, ← int.coe_nat_succ, coe_nat_le_coe_nat_iff], reflexivity end

lemma lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
(coe_nat_lt_coe_nat_iff  _ _).mp h

lemma coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
(coe_nat_lt_coe_nat_iff _ _).mpr h

/- show that the integers form an ordered additive group -/

protected lemma le_refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

protected lemma le_trans {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
le.elim h₁ (assume n, assume hn : a + n = b,
le.elim h₂ (assume m, assume hm : b + m = c,
begin apply le.intro, rw [← hm, ← hn, add_assoc], reflexivity end))

protected lemma le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
le.elim h₁ (assume n, assume hn : a + n = b,
le.elim h₂ (assume m, assume hm : b + m = a,
  have a + ↑(n + m) = a + 0, by rw [int.coe_nat_add, ← add_assoc, hn, hm, add_zero a],
  have (↑(n + m) : ℤ) = 0, from add_left_cancel this,
  have n + m = 0, from int.coe_nat_inj this,
  have n = 0, from nat.eq_zero_of_add_eq_zero_right this,
  show a = b, begin rw [← hn, this, int.coe_nat_zero, add_zero a] end))

protected lemma lt_irrefl (a : ℤ) : ¬ a < a :=
assume : a < a,
lt.elim this (assume n, assume hn : a + nat.succ n = a,
  have a + nat.succ n = a + 0, by rw [hn, add_zero],
  have nat.succ n = 0, from int.coe_nat_inj (add_left_cancel this),
  show false, from nat.succ_ne_zero _ this)

protected lemma ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b :=
(assume : a = b, absurd (begin rewrite this at h, exact h end) (int.lt_irrefl b))

lemma le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
lt.elim h (assume n, assume hn : a + nat.succ n = b, le.intro hn)

protected lemma lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (assume h, ⟨le_of_lt h, int.ne_of_lt h⟩)
  (assume ⟨aleb, aneb⟩,
    le.elim aleb (assume n, assume hn : a + n = b,
      have n ≠ 0,
        from (assume : n = 0, aneb begin rw [← hn, this, int.coe_nat_zero, add_zero] end),
      have n = nat.succ (nat.pred n),
        from eq.symm (nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero this)),
      lt.intro (begin rewrite this at hn, exact hn end)))

lemma lt_succ (a : ℤ) : a < a + 1 :=
int.le_refl (a + 1)

protected lemma add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
le.elim h (assume n, assume hn : a + n = b,
  le.intro (show c + a + n = c + b, begin rw [add_assoc, hn] end))

protected lemma add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
iff.mpr (int.lt_iff_le_and_ne _ _)
  (and.intro
    (int.add_le_add_left (le_of_lt h) _)
    (assume heq, int.lt_irrefl b begin rw add_left_cancel heq at h, exact h end))

protected lemma mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
le.elim ha (assume n, assume hn,
le.elim hb (assume m, assume hm,
  le.intro (show 0 + ↑n * ↑m = a * b, begin rw [← hn, ← hm], simp [zero_add] end)))

protected lemma mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
lt.elim ha (assume n, assume hn,
lt.elim hb (assume m, assume hm,
  lt.intro (show 0 + ↑(nat.succ (nat.succ n * m + n)) = a * b,
    begin rw [← hn, ← hm], simp [int.coe_nat_zero],
          rw [← int.coe_nat_mul], simp [nat.mul_succ, nat.succ_add] end)))

protected lemma zero_lt_one : (0 : ℤ) < 1 := trivial

protected lemma lt_iff_le_not_le {a b : ℤ} : a < b ↔ (a ≤ b ∧ ¬ b ≤ a) :=
begin
simp [int.lt_iff_le_and_ne], split; intro h,
{ cases h with hab hn, split,
  { assumption },
  { intro hba, simp [int.le_antisymm hab hba] at *, contradiction } },
{ cases h with hab hn, split,
  { assumption },
  { intro h, simp [*] at * } }
end

instance : decidable_linear_ordered_comm_ring int :=
{ le              := int.le,
  le_refl         := int.le_refl,
  le_trans        := @int.le_trans,
  le_antisymm     := @int.le_antisymm,
  lt              := int.lt,
  lt_iff_le_not_le := @int.lt_iff_le_not_le,
  add_le_add_left := @int.add_le_add_left,
  add_lt_add_left := @int.add_lt_add_left,
  zero_ne_one     := zero_ne_one,
  mul_nonneg      := @int.mul_nonneg,
  mul_pos         := @int.mul_pos,
  le_total        := int.le_total,
  zero_lt_one     := int.zero_lt_one,
  decidable_eq    := int.decidable_eq,
  decidable_le    := int.decidable_le,
  decidable_lt    := int.decidable_lt,
  ..int.comm_ring }

instance : decidable_linear_ordered_comm_group int :=
by apply_instance

lemma eq_nat_abs_of_zero_le {a : ℤ} (h : 0 ≤ a) : a = nat_abs a :=
let ⟨n, e⟩ := eq_coe_of_zero_le h in by rw e; refl

lemma le_nat_abs {a : ℤ} : a ≤ nat_abs a :=
or.elim (le_total 0 a)
  (λh, by rw eq_nat_abs_of_zero_le h; refl)
  (λh, le_trans h (coe_zero_le _))

lemma neg_succ_lt_zero (n : ℕ) : -[1+ n] < 0 :=
lt_of_not_ge $ λ h, let ⟨m, h⟩ := eq_coe_of_zero_le h in by contradiction

lemma eq_neg_succ_of_lt_zero : ∀ {a : ℤ}, a < 0 → ∃ n : ℕ, a = -[1+ n]
| (n : ℕ) h := absurd h (not_lt_of_ge (coe_zero_le _))
| -[1+ n] h := ⟨n, rfl⟩

/- more facts specific to int -/

theorem of_nat_nonneg (n : ℕ) : 0 ≤ of_nat n := trivial

theorem coe_succ_pos (n : nat) : (nat.succ n : ℤ) > 0 :=
coe_nat_lt_coe_nat_of_lt (nat.succ_pos _)

theorem exists_eq_neg_of_nat {a : ℤ} (H : a ≤ 0) : ∃n : ℕ, a = -n :=
let ⟨n, h⟩ := eq_coe_of_zero_le (neg_nonneg_of_nonpos H) in
⟨n, eq_neg_of_eq_neg h.symm⟩

theorem nat_abs_of_nonneg {a : ℤ} (H : a ≥ 0) : (nat_abs a : ℤ) = a :=
match a, eq_coe_of_zero_le H with ._, ⟨n, rfl⟩ := rfl end

theorem of_nat_nat_abs_of_nonpos {a : ℤ} (H : a ≤ 0) : (nat_abs a : ℤ) = -a :=
by rw [← nat_abs_neg, nat_abs_of_nonneg (neg_nonneg_of_nonpos H)]

theorem abs_eq_nat_abs : ∀ a : ℤ, abs a = nat_abs a
| (n : ℕ) := abs_of_nonneg $ coe_zero_le _
| -[1+ n] := abs_of_nonpos $ le_of_lt $ neg_succ_lt_zero _

theorem nat_abs_abs (a : ℤ) : nat_abs (abs a) = nat_abs a :=
by rw [abs_eq_nat_abs]; refl

theorem lt_of_add_one_le {a b : ℤ} (H : a + 1 ≤ b) : a < b := H

theorem add_one_le_of_lt {a b : ℤ} (H : a < b) : a + 1 ≤ b := H

theorem lt_add_one_of_le {a b : ℤ} (H : a ≤ b) : a < b + 1 :=
add_le_add_right H 1

theorem le_of_lt_add_one {a b : ℤ} (H : a < b + 1) : a ≤ b :=
le_of_add_le_add_right H

theorem sub_one_le_of_lt {a b : ℤ} (H : a ≤ b) : a - 1 < b :=
sub_right_lt_of_lt_add $ lt_add_one_of_le H

theorem lt_of_sub_one_le {a b : ℤ} (H : a - 1 < b) : a ≤ b :=
le_of_lt_add_one $ lt_add_of_sub_right_lt H

theorem le_sub_one_of_lt {a b : ℤ} (H : a < b) : a ≤ b - 1 :=
le_sub_right_of_add_le H

theorem lt_of_le_sub_one {a b : ℤ} (H : a ≤ b - 1) : a < b :=
add_le_of_le_sub_right H

theorem sign_of_succ (n : nat) : sign (nat.succ n) = 1 := rfl

theorem sign_eq_one_of_pos {a : ℤ} (h : 0 < a) : sign a = 1 :=
match a, eq_succ_of_zero_lt h with ._, ⟨n, rfl⟩ := rfl end

theorem sign_eq_neg_one_of_neg {a : ℤ} (h : a < 0) : sign a = -1 :=
match a, eq_neg_succ_of_lt_zero h with ._, ⟨n, rfl⟩ := rfl end

lemma eq_zero_of_sign_eq_zero : Π {a : ℤ}, sign a = 0 → a = 0
| 0 _ := rfl

theorem pos_of_sign_eq_one : ∀ {a : ℤ}, sign a = 1 → 0 < a
| (n+1:ℕ) _ := coe_nat_lt_coe_nat_of_lt (nat.succ_pos _)

theorem neg_of_sign_eq_neg_one : ∀ {a : ℤ}, sign a = -1 → a < 0
| (n+1:ℕ) h := match h with end
| 0       h := match h with end
| -[1+ n] _ := neg_succ_lt_zero _

theorem sign_eq_one_iff_pos (a : ℤ) : sign a = 1 ↔ 0 < a :=
⟨pos_of_sign_eq_one, sign_eq_one_of_pos⟩

theorem sign_eq_neg_one_iff_neg (a : ℤ) : sign a = -1 ↔ a < 0 :=
⟨neg_of_sign_eq_neg_one, sign_eq_neg_one_of_neg⟩

theorem sign_eq_zero_iff_zero (a : ℤ) : sign a = 0 ↔ a = 0 :=
⟨eq_zero_of_sign_eq_zero, λ h, by rw [h, sign_zero]⟩

theorem sign_mul_abs (a : ℤ) : sign a * abs a = a :=
by rw [abs_eq_nat_abs, sign_mul_nat_abs]

theorem eq_one_of_mul_eq_self_left {a b : ℤ} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
eq_of_mul_eq_mul_right Hpos (by rw [one_mul, H])

theorem eq_one_of_mul_eq_self_right {a b : ℤ} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
eq_of_mul_eq_mul_left Hpos (by rw [mul_one, H])

end int
