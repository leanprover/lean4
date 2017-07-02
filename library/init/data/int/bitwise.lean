/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import init.data.int.lemmas init.data.nat.bitwise init.data.bool.lemmas

universe u

namespace int

  def div2 : ℤ → ℤ
  | (of_nat n) := n.div2
  | -[1+ n] := -[1+ n.div2]

  def bodd : ℤ → bool
  | (of_nat n) := n.bodd
  | -[1+ n] := bnot (n.bodd)

  @[simp] lemma bodd_zero : bodd 0 = ff := rfl
  @[simp] lemma bodd_one : bodd 1 = tt := rfl
  @[simp] lemma bodd_two : bodd 2 = ff := rfl

  @[simp] lemma bodd_sub_nat_nat (m n : ℕ) : bodd (sub_nat_nat m n) = bxor m.bodd n.bodd :=
  by apply sub_nat_nat_elim m n (λ m n i, bodd i = bxor m.bodd n.bodd);
     intros i m; simp [bodd]; cases i.bodd; cases m.bodd; refl

  @[simp] lemma bodd_neg_of_nat (n : ℕ) : bodd (neg_of_nat n) = n.bodd :=
  by cases n; simp; refl

  @[simp] lemma bodd_neg (n : ℤ) : bodd (-n) = bodd n :=
  by cases n; unfold has_neg.neg; simp [int.coe_nat_eq, int.neg, bodd]

  @[simp] lemma bodd_add (m n : ℤ) : bodd (m + n) = bxor (bodd m) (bodd n) :=
  by cases m with m m; cases n with n n; unfold has_add.add; simp [int.add, bodd];
     cases m.bodd; cases n.bodd; refl

  @[simp] lemma bodd_mul (m n : ℤ) : bodd (m * n) = bodd m && bodd n :=
  by cases m with m m; cases n with n n; unfold has_mul.mul; simp [int.mul, bodd];
     cases m.bodd; cases n.bodd; refl

  theorem bodd_add_div2 : ∀ n, cond (bodd n) 1 0 + 2 * div2 n = n
  | (n : ℕ) :=
    by rw [show (cond (bodd n) 1 0 : ℤ) = (cond (bodd n) 1 0 : ℕ),
           by cases bodd n; refl]; exact congr_arg of_nat n.bodd_add_div2
  | -[1+ n] := begin
      refine eq.trans _ (congr_arg neg_succ_of_nat n.bodd_add_div2),
      dsimp [bodd], cases nat.bodd n; dsimp [cond, bnot, div2, int.mul],
      { change -[1+ 2 * nat.div2 n] = _, rw zero_add },
      { rw [zero_add, add_comm], refl }
    end

  theorem div2_val : ∀ n, div2 n = n / 2
  | (n : ℕ) := congr_arg of_nat n.div2_val
  | -[1+ n] := congr_arg neg_succ_of_nat n.div2_val

  def bit (b : bool) : ℤ → ℤ := cond b bit1 bit0

  lemma bit0_val (n : ℤ) : bit0 n = 2 * n := (two_mul _).symm

  lemma bit1_val (n : ℤ) : bit1 n = 2 * n + 1 := congr_arg (+(1:ℤ)) (bit0_val _)

  lemma bit_val (b n) : bit b n = 2 * n + cond b 1 0 :=
  by { cases b, apply (bit0_val n).trans (add_zero _).symm, apply bit1_val }

  lemma bit_decomp (n : ℤ) : bit (bodd n) (div2 n) = n :=
  (bit_val _ _).trans $ (add_comm _ _).trans $ bodd_add_div2 _

  def bit_cases_on {C : ℤ → Sort u} (n) (h : ∀ b n, C (bit b n)) : C n :=
  by rw -bit_decomp n; apply h

  @[simp] lemma bit_zero : bit ff 0 = 0 := rfl

  @[simp] lemma bit_coe_nat (b) (n : ℕ) : bit b n = nat.bit b n :=
  by rw [bit_val, nat.bit_val]; cases b; refl

  @[simp] lemma bit_neg_succ (b) (n : ℕ) : bit b -[1+ n] = -[1+ nat.bit (bnot b) n] :=
  by rw [bit_val, nat.bit_val]; cases b; refl

  @[simp] lemma bodd_bit (b n) : bodd (bit b n) = b :=
  by rw bit_val; simp; cases b; cases bodd n; refl

  @[simp] lemma div2_bit (b n) : div2 (bit b n) = n :=
  begin
    rw [bit_val, div2_val, add_comm, int.add_mul_div_left, (_ : (_/2:ℤ) = 0), zero_add],
    cases b, all_goals {exact dec_trivial}
  end

  def test_bit : ℤ → ℕ → bool
  | (m : ℕ) n := nat.test_bit m n
  | -[1+ m] n := bnot (nat.test_bit m n)

  @[simp] lemma test_bit_zero (b) : ∀ n, test_bit (bit b n) 0 = b
  | (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_zero
  | -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_zero];
                  clear test_bit_zero; cases b; refl

  @[simp] lemma test_bit_succ (m b) : ∀ n, test_bit (bit b n) (nat.succ m) = test_bit n m
  | (n : ℕ) := by rw [bit_coe_nat]; apply nat.test_bit_succ
  | -[1+ n] := by rw [bit_neg_succ]; dsimp [test_bit]; rw [nat.test_bit_succ]

  def nat_bitwise (f : bool → bool → bool) (m n : ℕ) : ℤ :=
  cond (f ff ff) -[1+ nat.bitwise (λx y, bnot (f x y)) m n] (nat.bitwise f m n)

  def bitwise (f : bool → bool → bool) : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat_bitwise f m n
  | (m : ℕ) -[1+ n] := nat_bitwise (λ x y, f x (bnot y)) m n
  | -[1+ m] (n : ℕ) := nat_bitwise (λ x y, f (bnot x) y) m n
  | -[1+ m] -[1+ n] := nat_bitwise (λ x y, f (bnot x) (bnot y)) m n

  def lnot : ℤ → ℤ
  | (m : ℕ) := -[1+ m]
  | -[1+ m] := m

  def lor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.ldiff n m]
  | -[1+ m] (n : ℕ) := -[1+ nat.ldiff m n]
  | -[1+ m] -[1+ n] := -[1+ nat.land m n]

  def land : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.land m n
  | (m : ℕ) -[1+ n] := nat.ldiff m n
  | -[1+ m] (n : ℕ) := nat.ldiff n m
  | -[1+ m] -[1+ n] := -[1+ nat.lor m n]

  def ldiff : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.ldiff m n
  | (m : ℕ) -[1+ n] := nat.land m n
  | -[1+ m] (n : ℕ) := -[1+ nat.lor m n]
  | -[1+ m] -[1+ n] := nat.ldiff n m

  def lxor : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.lxor m n
  | (m : ℕ) -[1+ n] := -[1+ nat.lxor m n]
  | -[1+ m] (n : ℕ) := -[1+ nat.lxor m n]
  | -[1+ m] -[1+ n] := nat.lxor m n

  def shiftl : ℤ → ℤ → ℤ
  | (m : ℕ) (n : ℕ) := nat.shiftl m n
  | (m : ℕ) -[1+ n] := nat.shiftr m (nat.succ n)
  | -[1+ m] (n : ℕ) := -[1+ nat.shiftl' tt m n]
  | -[1+ m] -[1+ n] := -[1+ nat.shiftr m (nat.succ n)]

  def shiftr (m n : ℤ) : ℤ := shiftl m (-n)

  private meta def bitwise_tac : tactic unit := `[
    apply funext, intro m,
    apply funext, intro n,
    cases m with m m; cases n with n n; try {refl},
    all_goals {
      apply congr_arg of_nat <|> apply congr_arg neg_succ_of_nat,
      try {dsimp [nat.land, nat.ldiff, nat.lor]},
      try {rw [
        show nat.bitwise (λ a b, a && bnot b) n m =
             nat.bitwise (λ a b, b && bnot a) m n, from
        congr_fun (congr_fun (@nat.bitwise_swap (λ a b, b && bnot a) rfl) n) m]},
      apply congr_arg (λ f, nat.bitwise f m n),
      apply funext, intro a,
      apply funext, intro b,
      cases a; cases b; refl
    },
    all_goals {unfold nat.land nat.ldiff nat.lor}
  ]

  theorem bitwise_or   : bitwise bor                  = lor   := by bitwise_tac
  theorem bitwise_and  : bitwise band                 = land  := by bitwise_tac
  theorem bitwise_diff : bitwise (λ a b, a && bnot b) = ldiff := by bitwise_tac
  theorem bitwise_xor  : bitwise bxor                 = lxor  := by bitwise_tac

  @[simp] lemma bitwise_bit (f : bool → bool → bool) (a m b n) :
    bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n) :=
  begin
    cases m with m m; cases n with n n;
    repeat { rw -int.coe_nat_eq <|> rw bit_coe_nat <|> rw bit_neg_succ };
    unfold bitwise nat_bitwise bnot;
    [ ginduction f ff ff with h,
      ginduction f ff tt with h,
      ginduction f tt ff with h,
      ginduction f tt tt with h ],
    all_goals {
      unfold cond, rw nat.bitwise_bit,
      repeat { rw bit_coe_nat <|> rw bit_neg_succ <|> rw bnot_bnot } },
    all_goals { unfold bnot {fail_if_unchanged := ff}; rw h; refl }
  end

  @[simp] lemma lor_bit (a m b n) : lor (bit a m) (bit b n) = bit (a || b) (lor m n) :=
  by rw [-bitwise_or, bitwise_bit]

  @[simp] lemma land_bit (a m b n) : land (bit a m) (bit b n) = bit (a && b) (land m n) :=
  by rw [-bitwise_and, bitwise_bit]

  @[simp] lemma ldiff_bit (a m b n) : ldiff (bit a m) (bit b n) = bit (a && bnot b) (ldiff m n) :=
  by rw [-bitwise_diff, bitwise_bit]

  @[simp] lemma lxor_bit (a m b n) : lxor (bit a m) (bit b n) = bit (bxor a b) (lxor m n) :=
  by rw [-bitwise_xor, bitwise_bit]

  @[simp] lemma lnot_bit (b) : ∀ n, lnot (bit b n) = bit (bnot b) (lnot n)
  | (n : ℕ) := by simp [lnot]
  | -[1+ n] := by simp [lnot]

  @[simp] lemma test_bit_bitwise (f : bool → bool → bool) (m n k) :
    test_bit (bitwise f m n) k = f (test_bit m k) (test_bit n k) :=
  begin
    revert m n; induction k with k IH; intros m n;
    apply bit_cases_on m; intros a m';
    apply bit_cases_on n; intros b n';
    rw bitwise_bit,
    { simp [test_bit_zero] },
    { simp [test_bit_succ, IH] }
  end

  @[simp] lemma test_bit_lor (m n k) : test_bit (lor m n) k = test_bit m k || test_bit n k :=
  by rw [-bitwise_or, test_bit_bitwise]

  @[simp] lemma test_bit_land (m n k) : test_bit (land m n) k = test_bit m k && test_bit n k :=
  by rw [-bitwise_and, test_bit_bitwise]

  @[simp] lemma test_bit_ldiff (m n k) : test_bit (ldiff m n) k = test_bit m k && bnot (test_bit n k) :=
  by rw [-bitwise_diff, test_bit_bitwise]

  @[simp] lemma test_bit_lxor (m n k) : test_bit (lxor m n) k = bxor (test_bit m k) (test_bit n k) :=
  by rw [-bitwise_xor, test_bit_bitwise]

  @[simp] lemma test_bit_lnot : ∀ n k, test_bit (lnot n) k = bnot (test_bit n k)
  | (n : ℕ) k := by simp [lnot, test_bit]
  | -[1+ n] k := by simp [lnot, test_bit]

  lemma shiftl_add : ∀ (m : ℤ) (n : ℕ) (k : ℤ), shiftl m (n + k) = shiftl (shiftl m n) k
  | (m : ℕ) n (k:ℕ) := congr_arg of_nat (nat.shiftl_add _ _ _)
  | -[1+ m] n (k:ℕ) := congr_arg neg_succ_of_nat (nat.shiftl'_add _ _ _ _)
  | (m : ℕ) n -[1+k] := sub_nat_nat_elim n k.succ
      (λ n k i, shiftl ↑m i = nat.shiftr (nat.shiftl m n) k)
      (λ i n, congr_arg coe $
        by rw [-nat.shiftl_sub, nat.add_sub_cancel_left]; apply nat.le_add_right)
      (λ i n, congr_arg coe $
        by rw [add_assoc, nat.shiftr_add, -nat.shiftl_sub, nat.sub_self]; refl)
  | -[1+ m] n -[1+k] := sub_nat_nat_elim n k.succ
      (λ n k i, shiftl -[1+ m] i = -[1+ nat.shiftr (nat.shiftl' tt m n) k])
      (λ i n, congr_arg neg_succ_of_nat $
        by rw [-nat.shiftl'_sub, nat.add_sub_cancel_left]; apply nat.le_add_right)
      (λ i n, congr_arg neg_succ_of_nat $
        by rw [add_assoc, nat.shiftr_add, -nat.shiftl'_sub, nat.sub_self]; refl)

  lemma shiftl_sub (m : ℤ) (n : ℕ) (k : ℤ) : shiftl m (n - k) = shiftr (shiftl m n) k :=
  shiftl_add _ _ _

  @[simp] lemma shiftl_neg (m n : ℤ) : shiftl m (-n) = shiftr m n := rfl
  @[simp] lemma shiftr_neg (m n : ℤ) : shiftr m (-n) = shiftl m n := by rw [-shiftl_neg, neg_neg]

  @[simp] lemma shiftl_coe_nat (m n : ℕ) : shiftl m n = nat.shiftl m n := rfl
  @[simp] lemma shiftr_coe_nat (m n : ℕ) : shiftr m n = nat.shiftr m n := by cases n; refl

  @[simp] lemma shiftl_neg_succ (m n : ℕ) : shiftl -[1+ m] n = -[1+ nat.shiftl' tt m n] := rfl
  @[simp] lemma shiftr_neg_succ (m n : ℕ) : shiftr -[1+ m] n = -[1+ nat.shiftr m n] := by cases n; refl

  lemma shiftr_add : ∀ (m : ℤ) (n k : ℕ), shiftr m (n + k) = shiftr (shiftr m n) k
  | (m : ℕ) n k := by rw [shiftr_coe_nat, shiftr_coe_nat,
                          -int.coe_nat_add, shiftr_coe_nat, nat.shiftr_add]
  | -[1+ m] n k := by rw [shiftr_neg_succ, shiftr_neg_succ,
                          -int.coe_nat_add, shiftr_neg_succ, nat.shiftr_add]

  lemma shiftl_eq_mul_pow : ∀ (m : ℤ) (n : ℕ), shiftl m n = m * 2 ^ n
  | (m : ℕ) n := congr_arg coe (nat.shiftl_eq_mul_pow _ _)
  | -[1+ m] n := @congr_arg ℕ ℤ _ _ (λi, -i) (nat.shiftl'_tt_eq_mul_pow _ _)

  lemma shiftr_eq_div_pow : ∀ (m : ℤ) (n : ℕ), shiftr m n = m / 2 ^ n
  | (m : ℕ) n := by rw shiftr_coe_nat; exact congr_arg coe (nat.shiftr_eq_div_pow _ _)
  | -[1+ m] n := begin
    rw [shiftr_neg_succ, neg_succ_of_nat_div, nat.shiftr_eq_div_pow], refl,
    exact coe_nat_lt_coe_nat_of_lt (nat.pos_pow_of_pos _ dec_trivial)
  end

  lemma one_shiftl (n : ℕ) : shiftl 1 n = (2 ^ n : ℕ) :=
  congr_arg coe (nat.one_shiftl _)

  @[simp] lemma zero_shiftl : ∀ n : ℤ, shiftl 0 n = 0
  | (n : ℕ) := congr_arg coe (nat.zero_shiftl _)
  | -[1+ n] := congr_arg coe (nat.zero_shiftr _)

  @[simp] lemma zero_shiftr (n) : shiftr 0 n = 0 := zero_shiftl _

end int
