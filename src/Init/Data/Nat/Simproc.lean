/-
Copyright (c) 2023 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Hendrix
-/
prelude
import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas

/-!
This contains lemmas used by the Nat simprocs for simplifying arithmetic
addition offsets.
-/
namespace Nat.Simproc

/- Sub proofs -/

theorem sub_add_eq_comm (a b c : Nat) : a - (b + c) = a - c - b := by
  rw [Nat.add_comm b c]
  exact Nat.sub_add_eq a c b

theorem add_sub_add_le (a c : Nat) {b d : Nat} (h : b ≤ d) : a + b - (c + d) = a - (c + (d-b)) := by
  induction b generalizing a c d with
  | zero =>
    simp
  | succ b ind =>
    match d with
    | 0 =>
      contradiction
    | d + 1 =>
      have g := Nat.le_of_succ_le_succ h
      rw [Nat.add_succ a, Nat.add_succ c, Nat.succ_sub_succ, Nat.succ_sub_succ,
          ind _ _ g]

theorem add_sub_add_ge (a c : Nat) {b d : Nat} (h : b ≥ d) : a + b - (c + d) = a + (b - d) - c := by
  rw [Nat.add_comm c d, Nat.sub_add_eq, Nat.add_sub_assoc h a]

theorem add_sub_le (a : Nat) {b c : Nat} (h : b ≤ c) : a + b - c = a - (c - b) := by
  have p := add_sub_add_le a 0 h
  simp only [Nat.zero_add] at p
  exact p

/- Eq proofs -/

theorem add_eq_gt (a : Nat) {b c : Nat} (h : b > c) : (a + b = c) = False :=
  eq_false (Nat.ne_of_gt (Nat.lt_of_lt_of_le h (le_add_left b a)))

theorem eq_add_gt (a : Nat) {b c : Nat} (h : c > a) : (a = b + c) = False := by
  rw [@Eq.comm Nat a (b + c)]
  exact add_eq_gt b h

theorem add_eq_add_le (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b = c + d) = (a = c + (d - b)) := by
  have g : b ≤ c + d := Nat.le_trans h (le_add_left d c)
  rw [← Nat.add_sub_assoc h, @Eq.comm _ a, Nat.sub_eq_iff_eq_add g, @Eq.comm _ (a + b)]

theorem add_eq_add_ge (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b = c + d) = (a + (b - d) = c) := by
  rw [@Eq.comm _ (a + b) _, add_eq_add_le c a h, @Eq.comm _ _ c]

theorem add_eq_le (a : Nat) {b c : Nat} (h : b ≤ c) : (a + b = c) = (a = c - b) := by
  have r := add_eq_add_le a 0 h
  simp only [Nat.zero_add] at r
  exact r

theorem eq_add_le {a : Nat} (b : Nat) {c : Nat} (h : c ≤ a) : (a = b + c) = (b = a - c) := by
  rw [@Eq.comm Nat a (b + c)]
  exact add_eq_le b h

/- Lemmas for lifting Eq proofs to beq -/

theorem beqEqOfEqEq {a b c d : Nat} (p : (a = b) = (c = d)) : (a == b) = (c == d) := by
  simp only [Bool.beq_eq_decide_eq, p]

theorem beqFalseOfEqFalse {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  simp [Bool.beq_eq_decide_eq, p]

theorem bneEqOfEqEq {a b c d : Nat} (p : (a = b) = (c = d)) : (a != b) = (c != d) := by
  simp only [bne, beqEqOfEqEq p]

theorem bneTrueOfEqFalse {a b : Nat} (p : (a = b) = False) : (a != b) = true := by
  simp [bne, beqFalseOfEqFalse p]

/- le proofs -/

theorem add_le_add_le (a c : Nat) {b d : Nat} (h : b ≤ d) : (a + b ≤ c + d) = (a ≤ c + (d - b)) := by
  rw [← Nat.add_sub_assoc h, Nat.le_sub_iff_add_le]
  exact Nat.le_trans h (le_add_left d c)

theorem add_le_add_ge (a c : Nat) {b d : Nat} (h : b ≥ d) : (a + b ≤ c + d) = (a + (b - d) ≤ c) := by
  rw [← Nat.add_sub_assoc h, Nat.sub_le_iff_le_add]

theorem add_le_le (a : Nat) {b c : Nat} (h : b ≤ c) : (a + b ≤ c) = (a ≤ c - b) := by
  have r := add_le_add_le a 0 h
  simp only [Nat.zero_add] at r
  exact r

theorem add_le_gt (a : Nat) {b c : Nat} (h : b > c) : (a + b ≤ c) = False :=
  eq_false (Nat.not_le_of_gt (Nat.lt_of_lt_of_le h (le_add_left b a)))

theorem le_add_le (a : Nat) {b c : Nat} (h : a ≤ c) : (a ≤ b + c) = True :=
  eq_true (Nat.le_trans h (le_add_left c b))

theorem le_add_ge (a : Nat) {b c : Nat} (h : a ≥ c) : (a ≤ b + c) = (a - c ≤ b) := by
  have r := add_le_add_ge 0 b h
  simp only [Nat.zero_add] at r
  exact r

end Nat.Simproc
