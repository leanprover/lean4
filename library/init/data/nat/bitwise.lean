/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import init.data.nat.lemmas init.meta.well_founded_tactics

universe u

namespace nat

def bodd_div2 : ℕ → bool × ℕ
| 0        := (ff, 0)
| (succ n) :=
    match bodd_div2 n with
    | (ff, m) := (tt, m)
    | (tt, m) := (ff, succ m)
    end

def div2 (n : ℕ) : ℕ := (bodd_div2 n).2

def bodd (n : ℕ) : bool := (bodd_div2 n).1

@[simp] lemma bodd_zero : bodd 0 = ff := rfl
@[simp] lemma bodd_one : bodd 1 = tt := rfl
@[simp] lemma bodd_two : bodd 2 = ff := rfl

@[simp] lemma bodd_succ (n : ℕ) : bodd (succ n) = bnot (bodd n) :=
by unfold bodd bodd_div2; cases bodd_div2 n; cases fst; refl

@[simp] lemma bodd_add (m n : ℕ) : bodd (m + n) = bxor (bodd m) (bodd n) :=
begin
    induction n with n IH,
    { simp, cases bodd m; refl },
    { simp [IH], cases bodd m; cases bodd n; refl }
end

@[simp] lemma bodd_mul (m n : ℕ) : bodd (m * n) = bodd m && bodd n :=
begin
    induction n with n IH,
    { simp, cases bodd m; refl },
    { simp [mul_succ, IH], cases bodd m; cases bodd n; refl }
end

lemma mod_two_of_bodd (n : ℕ) : n % 2 = cond (bodd n) 1 0 :=
begin
    have := congr_arg bodd (mod_add_div n 2),
    simp [bnot] at this,
    rw [show ∀ b, ff && b = ff, by intros; cases b; refl,
        show ∀ b, bxor b ff = b, by intros; cases b; refl] at this,
    rw [← this],
    cases mod_two_eq_zero_or_one n with h h; rw h; refl
end

@[simp] lemma div2_zero : div2 0 = 0 := rfl
@[simp] lemma div2_one : div2 1 = 0 := rfl
@[simp] lemma div2_two : div2 2 = 1 := rfl

@[simp] lemma div2_succ (n : ℕ) : div2 (succ n) = cond (bodd n) (succ (div2 n)) (div2 n) :=
by unfold bodd div2 bodd_div2; cases bodd_div2 n; cases fst; refl

local attribute [simp] add_comm add_assoc add_left_comm mul_comm mul_assoc mul_left_comm

theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
| 0        := rfl
| (succ n) := begin
    simp,
    refine eq.trans _ (congr_arg succ (bodd_add_div2 n)),
    cases bodd n; simp [cond, bnot],
    { rw add_comm; refl },
    { rw [succ_mul, add_comm 1] }
end

theorem div2_val (n) : div2 n = n / 2 :=
by refine eq_of_mul_eq_mul_left dec_trivial
      (nat.add_left_cancel (eq.trans _ (mod_add_div n 2).symm));
     rw [mod_two_of_bodd, bodd_add_div2]

def bit (b : bool) : ℕ → ℕ := cond b bit1 bit0

lemma bit0_val (n : nat) : bit0 n = 2 * n := (two_mul _).symm

lemma bit1_val (n : nat) : bit1 n = 2 * n + 1 := congr_arg succ (bit0_val _)

lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
by { cases b, apply bit0_val, apply bit1_val }

lemma bit_decomp (n : nat) : bit (bodd n) (div2 n) = n :=
(bit_val _ _).trans $ (add_comm _ _).trans $ bodd_add_div2 _

def bit_cases_on {C : nat → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
by rw [← bit_decomp n]; apply h

@[simp] lemma bit_zero : bit ff 0 = 0 := rfl

def shiftl' (b : bool) (m : ℕ) : ℕ → ℕ
| 0     := m
| (n+1) := bit b (shiftl' n)

def shiftl : ℕ → ℕ → ℕ := shiftl' ff

@[simp] theorem shiftl_zero (m) : shiftl m 0 = m := rfl
@[simp] theorem shiftl_succ (m n) : shiftl m (n + 1) = bit0 (shiftl m n) := rfl

def shiftr : ℕ → ℕ → ℕ
| m 0     := m
| m (n+1) := div2 (shiftr m n)

def test_bit (m n : ℕ) : bool := bodd (shiftr m n)

def binary_rec {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) : Π n, C n
| n := if n0 : n = 0 then by rw n0; exact z else let n' := div2 n in
    have n' < n, begin
      change div2 n < n, rw div2_val,
      apply (div_lt_iff_lt_mul _ _ (succ_pos 1)).2,
      have := nat.mul_lt_mul_of_pos_left (lt_succ_self 1)
        (lt_of_le_of_ne (zero_le _) (ne.symm n0)),
      rwa mul_one at this
    end,
    by rw [← show bit (bodd n) n' = n, from bit_decomp n]; exact
    f (bodd n) n' (binary_rec n')

def size : ℕ → ℕ := binary_rec 0 (λ_ _, succ)

def bits : ℕ → list bool := binary_rec [] (λb _ IH, b :: IH)

def bitwise (f : bool → bool → bool) : ℕ → ℕ → ℕ :=
binary_rec
    (λn, cond (f ff tt) n 0)
    (λa m Ia, binary_rec
      (cond (f tt ff) (bit a m) 0)
      (λb n _, bit (f a b) (Ia n)))

def lor   : ℕ → ℕ → ℕ := bitwise bor
def land  : ℕ → ℕ → ℕ := bitwise band
def ldiff : ℕ → ℕ → ℕ := bitwise (λ a b, a && bnot b)
def lxor  : ℕ → ℕ → ℕ := bitwise bxor

@[simp] lemma binary_rec_zero {C : nat → Sort u} (z : C 0) (f : ∀ b n, C n → C (bit b n)) :
    binary_rec z f 0 = z :=
by {rw [binary_rec], refl}

/- bitwise ops -/

lemma bodd_bit (b n) : bodd (bit b n) = b :=
by rw bit_val; simp; cases b; cases bodd n; refl

lemma div2_bit (b n) : div2 (bit b n) = n :=
by rw [bit_val, div2_val, add_comm, add_mul_div_left, div_eq_of_lt, zero_add];
   cases b; exact dec_trivial

lemma shiftl'_add (b m n) : ∀ k, shiftl' b m (n + k) = shiftl' b (shiftl' b m n) k
| 0     := rfl
| (k+1) := congr_arg (bit b) (shiftl'_add k)

lemma shiftl_add : ∀ m n k, shiftl m (n + k) = shiftl (shiftl m n) k := shiftl'_add _

lemma shiftr_add (m n) : ∀ k, shiftr m (n + k) = shiftr (shiftr m n) k
| 0     := rfl
| (k+1) := congr_arg div2 (shiftr_add k)

lemma shiftl'_sub (b m) : ∀ {n k}, k ≤ n → shiftl' b m (n - k) = shiftr (shiftl' b m n) k
| n     0     h := rfl
| (n+1) (k+1) h := begin
  simp [shiftl'], rw [add_comm, shiftr_add],
  simp [shiftr, div2_bit],
  apply shiftl'_sub (nat.le_of_succ_le_succ h)
end

lemma shiftl_sub : ∀ m {n k}, k ≤ n → shiftl m (n - k) = shiftr (shiftl m n) k := shiftl'_sub _

lemma shiftl_eq_mul_pow (m) : ∀ n, shiftl m n = m * 2 ^ n
| 0     := (mul_one _).symm
| (k+1) := show bit0 (shiftl m k) = m * (2^k * 2), by rw [bit0_val, shiftl_eq_mul_pow]; simp

lemma shiftl'_tt_eq_mul_pow (m) : ∀ n, shiftl' tt m n + 1 = (m + 1) * 2 ^ n
| 0     := by simp [shiftl, shiftl']
| (k+1) := begin
  change bit1 (shiftl' tt m k) + 1 = (m + 1) * (2^k * 2),
  rw bit1_val,
  change 2 * (shiftl' tt m k + 1) = _,
  rw shiftl'_tt_eq_mul_pow; simp
end

lemma one_shiftl (n) : shiftl 1 n = 2 ^ n :=
(shiftl_eq_mul_pow _ _).trans (one_mul _)

@[simp] lemma zero_shiftl (n) : shiftl 0 n = 0 :=
(shiftl_eq_mul_pow _ _).trans (zero_mul _)

lemma shiftr_eq_div_pow (m) : ∀ n, shiftr m n = m / 2 ^ n
| 0     := (nat.div_one _).symm
| (k+1) := (congr_arg div2 (shiftr_eq_div_pow k)).trans $
           by rw [div2_val, nat.div_div_eq_div_mul]; refl

@[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 :=
(shiftr_eq_div_pow _ _).trans (nat.zero_div _)

@[simp] lemma test_bit_zero (b n) : test_bit (bit b n) 0 = b := bodd_bit _ _

lemma test_bit_succ (m b n) : test_bit (bit b n) (succ m) = test_bit n m :=
have bodd (shiftr (shiftr (bit b n) 1) m) = bodd (shiftr n m),
  by dsimp [shiftr]; rw div2_bit,
by rw [← shiftr_add, add_comm] at this; exact this

lemma binary_rec_eq {C : nat → Sort u} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
  (h : f ff 0 z = z) (b n) :
  binary_rec z f (bit b n) = f b n (binary_rec z f n) :=
begin
  rw [binary_rec],
  with_cases { by_cases bit b n = 0 },
  case pos : h' {
    simp [dif_pos h'],
    generalize : binary_rec._main._pack._proof_1 (bit b n) h' = e,
    revert e,
    have bf := bodd_bit b n,
    have n0 := div2_bit b n,
    rw h' at bf n0,
    simp at bf n0,
    rw [← bf, ← n0, binary_rec_zero],
    intros, exact h.symm },
  case neg : h' {
    simp [dif_neg h'],
    generalize : binary_rec._main._pack._proof_2 (bit b n) = e,
    revert e,
    rw [bodd_bit, div2_bit],
    intros, refl}
end

lemma bitwise_bit_aux {f : bool → bool → bool} (h : f ff ff = ff) :
  @binary_rec (λ_, ℕ)
    (cond (f tt ff) (bit ff 0) 0)
    (λ b n _, bit (f ff b) (cond (f ff tt) n 0)) =
  λ (n : ℕ), cond (f ff tt) n 0 :=
begin
  funext n,
  apply bit_cases_on n, intros b n, rw [binary_rec_eq],
  { cases b; try {rw h}; induction fft : f ff tt; simp [cond]; refl },
  { rw [h, show cond (f ff tt) 0 0 = 0, by cases f ff tt; refl,
           show cond (f tt ff) (bit ff 0) 0 = 0, by cases f tt ff; refl]; refl }
end

@[simp] lemma bitwise_zero_left (f : bool → bool → bool) (n) :
  bitwise f 0 n = cond (f ff tt) n 0 :=
by unfold bitwise; rw [binary_rec_zero]

@[simp] lemma bitwise_zero_right (f : bool → bool → bool) (h : f ff ff = ff) (m) :
  bitwise f m 0 = cond (f tt ff) m 0 :=
by unfold bitwise; apply bit_cases_on m; intros;
   rw [binary_rec_eq, binary_rec_zero]; exact bitwise_bit_aux h

@[simp] lemma bitwise_zero (f : bool → bool → bool) :
  bitwise f 0 0 = 0 :=
by rw bitwise_zero_left; cases f ff tt; refl

@[simp] lemma bitwise_bit {f : bool → bool → bool} (h : f ff ff = ff) (a m b n) :
  bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
begin
  unfold bitwise,
  rw [binary_rec_eq, binary_rec_eq],
  { induction ftf : f tt ff; dsimp [cond],
    rw [show f a ff = ff, by cases a; assumption],
    apply @congr_arg _ _ _ 0 (bit ff), tactic.swap,
    rw [show f a ff = a, by cases a; assumption],
    apply congr_arg (bit a),
    all_goals {
      apply bit_cases_on m, intros a m,
      rw [binary_rec_eq, binary_rec_zero],
      rw [← bitwise_bit_aux h, ftf], refl } },
  { exact bitwise_bit_aux h }
end

theorem bitwise_swap {f : bool → bool → bool} (h : f ff ff = ff) :
  bitwise (function.swap f) = function.swap (bitwise f) :=
begin
  funext m n, revert n,
  dsimp [function.swap],
  apply binary_rec _ (λ a m' IH, _) m; intro n,
  { rw [bitwise_zero_left, bitwise_zero_right], exact h },
  apply bit_cases_on n; intros b n',
  rw [bitwise_bit, bitwise_bit, IH]; exact h
end

@[simp] lemma lor_bit : ∀ (a m b n),
  lor (bit a m) (bit b n) = bit (a || b) (lor m n) := bitwise_bit rfl
@[simp] lemma land_bit : ∀ (a m b n),
  land (bit a m) (bit b n) = bit (a && b) (land m n) := bitwise_bit rfl
@[simp] lemma ldiff_bit : ∀ (a m b n),
  ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) := bitwise_bit rfl
@[simp] lemma lxor_bit : ∀ (a m b n),
  lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) := bitwise_bit rfl

@[simp] lemma test_bit_bitwise {f : bool → bool → bool} (h : f ff ff = ff) (m n k) :
  test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
begin
  revert m n; induction k with k IH; intros m n;
  apply bit_cases_on m; intros a m';
  apply bit_cases_on n; intros b n';
  rw bitwise_bit h,
  { simp [test_bit_zero] },
  { simp [test_bit_succ, IH] }
end

@[simp] lemma test_bit_lor : ∀ (m n k),
  test_bit (lor m n) k = test_bit m k || test_bit n k := test_bit_bitwise rfl
@[simp] lemma test_bit_land : ∀ (m n k),
  test_bit (land m n) k = test_bit m k && test_bit n k := test_bit_bitwise rfl
@[simp] lemma test_bit_ldiff : ∀ (m n k),
  test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) := test_bit_bitwise rfl
@[simp] lemma test_bit_lxor : ∀ (m n k),
  test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) := test_bit_bitwise rfl
end nat
