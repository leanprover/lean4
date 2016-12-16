/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The order relation on the integers.
-/
prelude
import init.data.int.basic

namespace int

private def nonneg (a : ℤ) : Prop := int.cases_on a (take n, true) (take n, false)

protected def le (a b : ℤ) : Prop := nonneg (b - a)

instance : has_le int := has_le.mk int.le

protected def lt (a b : ℤ) : Prop := (a + 1) ≤ b

instance : has_lt int := has_lt.mk int.lt

private def decidable_nonneg (a : ℤ) : decidable (nonneg a) :=
int.cases_on a (take a, decidable.true) (take a, decidable.false)

instance decidable_le (a b : ℤ) : decidable (a ≤ b) := decidable_nonneg _

instance decidable_lt (a b : ℤ) : decidable (a < b) := decidable_nonneg _

theorem lt_iff_add_one_le (a b : ℤ) : a < b ↔ a + 1 ≤ b := iff.refl _

private theorem nonneg.elim {a : ℤ} : nonneg a → ∃ n : ℕ, a = n :=
int.cases_on a (take n H, exists.intro n rfl) (take n', false.elim)

private theorem nonneg_or_nonneg_neg (a : ℤ) : nonneg a ∨ nonneg (-a) :=
int.cases_on a (take n, or.inl trivial) (take n, or.inr trivial)

theorem le.intro {a b : ℤ} {n : ℕ} (h : a + n = b) : a ≤ b :=
have ↑n = b - a, begin rw -h, simp end,
show nonneg (b - a), from this ▸ trivial

theorem le.dest {a b : ℤ} (h : a ≤ b) : ∃ n : ℕ, a + n = b :=
match (nonneg.elim h) with
| ⟨n, h₁⟩ := exists.intro n begin rw [-h₁, add_comm], simp end
end

theorem le.elim {a b : ℤ} (h : a ≤ b) {P : Prop} (h' : ∀ n : ℕ, a + ↑n = b → P) : P :=
exists.elim (le.dest h) h'

protected theorem le_total (a b : ℤ) : a ≤ b ∨ b ≤ a :=
or.imp_right
  (assume H : nonneg (-(b - a)),
   have -(b - a) = a - b, by simp,
   show nonneg (a - b), from this ▸ H)
  (nonneg_or_nonneg_neg (b - a))

theorem coe_nat_le_coe_nat_of_le {m n : ℕ} (h : m ≤ n) : (↑m : ℤ) ≤ ↑n :=
match nat.le.dest h with
| ⟨k, (hk : m + k = n)⟩ := le.intro (begin rw [-hk], reflexivity end)
end

theorem le_of_coe_nat_le_coe_nat {m n : ℕ} (h : (↑m : ℤ) ≤ ↑n) : m ≤ n :=
le.elim h (take k, assume hk : ↑m + ↑k = ↑n,
  have m + k = n, from int.coe_nat_inj ((int.coe_nat_add m k)^.trans hk),
  nat.le.intro this)

theorem coe_nat_le_coe_nat_iff (m n : ℕ) : (↑m : ℤ) ≤ ↑n ↔ m ≤ n :=
iff.intro le_of_coe_nat_le_coe_nat coe_nat_le_coe_nat_of_le

theorem lt_add_succ (a : ℤ) (n : ℕ) : a < a + ↑(nat.succ n) :=
le.intro (show a + 1 + n = a + nat.succ n, begin simp [int.coe_nat_eq], reflexivity end)

theorem lt.intro {a b : ℤ} {n : ℕ} (h : a + nat.succ n = b) : a < b :=
h ▸ lt_add_succ a n

theorem lt.dest {a b : ℤ} (h : a < b) : ∃ n : ℕ, a + ↑(nat.succ n) = b :=
le.elim h (take n, assume hn : a + 1 + n = b,
    exists.intro n begin rw [-hn, add_assoc, add_comm (1 : int)], reflexivity end)

theorem lt.elim {a b : ℤ} (h : a < b) {P : Prop} (h' : ∀ n : ℕ, a + ↑(nat.succ n) = b → P) : P :=
exists.elim (lt.dest h) h'

theorem coe_nat_lt_coe_nat_iff (n m : ℕ) : (↑n : ℤ) < ↑m ↔ n < m :=
begin rw [lt_iff_add_one_le, -int.coe_nat_succ, coe_nat_le_coe_nat_iff], reflexivity end

theorem lt_of_coe_nat_lt_coe_nat {m n : ℕ} (h : (↑m : ℤ) < ↑n) : m < n :=
(coe_nat_lt_coe_nat_iff  _ _)^.mp h

theorem coe_nat_lt_coe_nat_of_lt {m n : ℕ} (h : m < n) : (↑m : ℤ) < ↑n :=
(coe_nat_lt_coe_nat_iff _ _)^.mpr h

/- show that the integers form an ordered additive group -/

protected theorem le_refl (a : ℤ) : a ≤ a :=
le.intro (add_zero a)

protected theorem le_trans {a b c : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
le.elim h₁ (take n, assume hn : a + n = b,
le.elim h₂ (take m, assume hm : b + m = c,
begin apply le.intro, rw [-hm, -hn, add_assoc], reflexivity end))

protected theorem le_antisymm {a b : ℤ} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b :=
le.elim h₁ (take n, assume hn : a + n = b,
le.elim h₂ (take m, assume hm : b + m = a,
  have a + ↑(n + m) = a + 0, by rw [int.coe_nat_add, -add_assoc, hn, hm, add_zero a],
  have (↑(n + m) : ℤ) = 0, from add_left_cancel this,
  have n + m = 0, from int.coe_nat_inj this,
  have n = 0, from nat.eq_zero_of_add_eq_zero_right this,
  show a = b, begin rw [-hn, this, int.coe_nat_zero, add_zero a] end))

protected theorem lt_irrefl (a : ℤ) : ¬ a < a :=
suppose a < a,
lt.elim this (take n, assume hn : a + nat.succ n = a,
  have a + nat.succ n = a + 0, by rw [hn, add_zero],
  have nat.succ n = 0, from int.coe_nat_inj (add_left_cancel this),
  show false, from nat.succ_ne_zero _ this)

protected theorem ne_of_lt {a b : ℤ} (h : a < b) : a ≠ b :=
(suppose a = b, absurd (begin rewrite this at h, exact h end) (int.lt_irrefl b))

theorem le_of_lt {a b : ℤ} (h : a < b) : a ≤ b :=
lt.elim h (take n, assume hn : a + nat.succ n = b, le.intro hn)

protected theorem lt_iff_le_and_ne (a b : ℤ) : a < b ↔ (a ≤ b ∧ a ≠ b) :=
iff.intro
  (assume h, ⟨le_of_lt h, int.ne_of_lt h⟩)
  (assume ⟨aleb, aneb⟩,
    le.elim aleb (take n, assume hn : a + n = b,
      have n ≠ 0,
        from (suppose n = 0, aneb begin rw [-hn, this, int.coe_nat_zero, add_zero] end),
      have n = nat.succ (nat.pred n),
        from eq.symm (nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero this)),
      lt.intro (begin rewrite this at hn, exact hn end)))

protected theorem le_iff_lt_or_eq (a b : ℤ) : a ≤ b ↔ (a < b ∨ a = b) :=
iff.intro
  (assume h,
    decidable.by_cases
      (suppose a = b, or.inr this)
      (suppose a ≠ b,
        le.elim h (take n, assume hn : a + n = b,
          have n ≠ 0, from
            (suppose n = 0, ‹a ≠ b› begin rw [-hn, this, int.coe_nat_zero, add_zero] end),
          have n = nat.succ (nat.pred n),
            from eq.symm (nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero this)),
          or.inl (lt.intro (begin rewrite this at hn, exact hn end)))))
  (assume h,
    or.elim h
      (assume h', le_of_lt h')
      (assume h', h' ▸ int.le_refl a))

theorem lt_succ (a : ℤ) : a < a + 1 :=
int.le_refl (a + 1)

protected theorem add_le_add_left {a b : ℤ} (h : a ≤ b) (c : ℤ) : c + a ≤ c + b :=
le.elim h (take n, assume hn : a + n = b,
  le.intro (show c + a + n = c + b, begin rw [add_assoc, hn] end))

protected theorem add_lt_add_left {a b : ℤ} (h : a < b) (c : ℤ) : c + a < c + b :=
iff.mpr (int.lt_iff_le_and_ne _ _)
  (and.intro
    (int.add_le_add_left (le_of_lt h) _)
    (take heq, int.lt_irrefl b begin rw add_left_cancel heq at h, exact h end))

protected theorem mul_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
le.elim ha (take n, assume hn,
le.elim hb (take m, assume hm,
  le.intro (show 0 + ↑n * ↑m = a * b, begin rw [-hn, -hm], repeat {rw zero_add} end)))

protected theorem mul_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
lt.elim ha (take n, assume hn,
lt.elim hb (take m, assume hm,
  lt.intro (show 0 + ↑(nat.succ (nat.succ n * m + n)) = a * b,
    begin rw [-hn, -hm], repeat {rw int.coe_nat_zero}, simp,
          rw [-int.coe_nat_mul], simp [nat.mul_succ, nat.succ_add] end)))

protected theorem zero_lt_one : (0 : ℤ) < 1 := trivial

protected theorem not_le_of_gt {a b : ℤ} (h : a < b) : ¬ b ≤ a :=
assume hba : b ≤ a,
have a = b, from int.le_antisymm (le_of_lt h) hba,
show false, from int.lt_irrefl b (begin rw this at h, exact h end)

protected theorem lt_of_lt_of_le {a b c : ℤ} (hab : a < b) (hbc : b ≤ c) : a < c :=
have hac : a ≤ c, from int.le_trans (le_of_lt hab) hbc,
iff.mpr
  (int.lt_iff_le_and_ne _ _)
  (and.intro hac (assume heq, int.not_le_of_gt begin rw -heq, assumption end hbc))

protected theorem lt_of_le_of_lt  {a b c : ℤ} (hab : a ≤ b) (hbc : b < c) : a < c :=
have hac : a ≤ c, from int.le_trans hab (le_of_lt hbc),
iff.mpr
  (int.lt_iff_le_and_ne _ _)
  (and.intro hac (assume heq, int.not_le_of_gt begin rw heq, exact hbc end hab))

instance : linear_ordered_ring int :=
{ int.comm_ring with
  le := int.le,
  le_refl := int.le_refl,
  le_trans := @int.le_trans,
  le_antisymm := @int.le_antisymm,
  lt := int.lt,
  le_of_lt := @int.le_of_lt,
  lt_of_lt_of_le := @int.lt_of_lt_of_le,
  lt_of_le_of_lt := @int.lt_of_le_of_lt,
  lt_irrefl := int.lt_irrefl,
  add_le_add_left := @int.add_le_add_left,
  add_lt_add_left := @int.add_lt_add_left,
  zero_ne_one := int.zero_ne_one,
  mul_nonneg := @int.mul_nonneg,
  mul_pos := @int.mul_pos,
  le_iff_lt_or_eq := int.le_iff_lt_or_eq,
  le_total := int.le_total,
  zero_lt_one := int.zero_lt_one }

end int

-- TODO(Jeremy): add more facts specific to the integers
