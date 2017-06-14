/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

prelude
import init.data.int.basic init.data.nat.bitwise

universe u

namespace int

  def test_bit : ℤ → ℕ → bool
  | (m : ℕ) n := nat.test_bit m n
  | -[1+ m] n := bnot (nat.test_bit m n)

  def nat_bitwise (f : bool → bool → bool) (m n : ℕ) : ℤ :=
  cond (f ff ff) -[1+ nat.bitwise (λx y, bnot (f x y)) m n] (nat.bitwise f m n)

  def bitwise (f : bool → bool → bool) : ℤ → ℤ → ℤ
  | (of_nat m) (of_nat n) := nat_bitwise f m n
  | (of_nat m) -[1+ n]    := nat_bitwise (λ x y, f x (bnot y)) m n
  | -[1+ m]    (of_nat n) := nat_bitwise (λ x y, f (bnot x) y) m n
  | -[1+ m]    -[1+ n]    := nat_bitwise (λ x y, f (bnot x) (bnot y)) m n

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
  | -[1+ m] (n : ℕ) := -[1+ nat.shiftl m n]
  | -[1+ m] -[1+ n] := -[1+ nat.shiftr m (nat.succ n)]

  def shiftr (m n : ℤ) : ℤ := shiftl m (-n)

  lemma ldiff_swap (m n) : nat.bitwise (λ a b, a && bnot b) m n
    = nat.bitwise (λ a b, b && bnot a) n m :=
  congr_fun (congr_fun (@nat.bitwise_swap (λ a b, b && bnot a) rfl) m) n

  private meta def bitwise_tac : tactic unit := `[
    apply funext, intro m,
    apply funext, intro n,
    cases m with m m; cases n with n n; try {refl},
    all_goals {
      apply congr_arg of_nat <|> apply congr_arg neg_succ_of_nat,
      dsimp [nat.land, nat.ldiff, nat.lor],
      try {rw ldiff_swap n m},
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

end int
