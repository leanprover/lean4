/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Data.Int.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.Gcd
import Init.Data.Int.LemmasAux
public section

/-!
Kernel-reduction variants of `Int` arithmetic, written with `Int.rec`, `Bool.rec`, and `Nat`
operations that the kernel evaluates on literals, together with proofs that they agree with the
standard operations. They avoid `match` and explicit recursion, which the kernel unfolds slowly.
Used in certificates that the kernel checks by evaluation, such as those of `lia`.
-/

namespace Int

/-- `subNatNat` for kernel reduction. -/
@[expose] protected noncomputable def subNatNat_k (m n : Nat) : Int :=
  Bool.rec (Int.negSucc (Nat.sub (Nat.sub n m) 1)) (Int.ofNat (Nat.sub m n)) (Nat.ble n m)

/-- `negOfNat` for kernel reduction. -/
@[expose] protected noncomputable def negOfNat_k (k : Nat) : Int :=
  Bool.rec (Int.negSucc (Nat.sub k 1)) (Int.ofNat 0) (Nat.beq k 0)

/-- `-a` for kernel reduction. -/
@[expose] protected noncomputable def neg_k (a : Int) : Int :=
  Int.rec (fun n => Int.negOfNat_k n) (fun n => Int.ofNat (Nat.add n 1)) a

/-- `a + b` for kernel reduction. -/
@[expose] protected noncomputable def add_k (a b : Int) : Int :=
  Int.rec
    (fun m => Int.rec (fun n => Int.ofNat (Nat.add m n)) (fun n => Int.subNatNat_k m (Nat.add n 1)) b)
    (fun m => Int.rec (fun n => Int.subNatNat_k n (Nat.add m 1)) (fun n => Int.negSucc (Nat.add (Nat.add m n) 1)) b)
    a

/-- `a * b` for kernel reduction. -/
@[expose] protected noncomputable def mul_k (a b : Int) : Int :=
  Int.rec
    (fun m => Int.rec (fun n => Int.ofNat (Nat.mul m n)) (fun n => Int.negOfNat_k (Nat.mul m (Nat.add n 1))) b)
    (fun m => Int.rec (fun n => Int.negOfNat_k (Nat.mul (Nat.add m 1) n)) (fun n => Int.ofNat (Nat.mul (Nat.add m 1) (Nat.add n 1))) b)
    a

/-- `a.natAbs` for kernel reduction. -/
@[expose] protected noncomputable def natAbs_k (a : Int) : Nat :=
  Int.rec (fun m => m) (fun m => Nat.add m 1) a

/-- `a == 0` for kernel reduction. Unlike `Int.beq' a 0`, it inspects `a` only once. -/
@[expose] protected noncomputable def beqZero_k (a : Int) : Bool :=
  Int.rec (fun m => Nat.beq m 0) (fun _ => false) a

/-- `a - b` for kernel reduction. -/
@[expose] protected noncomputable def sub_k (a b : Int) : Int :=
  Int.add_k a (Int.neg_k b)

/-- `a != 0` for kernel reduction. -/
@[expose] protected noncomputable def bneZero_k (a : Int) : Bool :=
  Int.rec (fun m => Nat.blt 0 m) (fun _ => true) a

/-- `a % b` for kernel reduction. -/
@[expose] protected noncomputable def emod_k (a b : Int) : Int :=
  Int.rec (fun m => Int.ofNat (Nat.mod m (Int.natAbs_k b)))
    (fun m => Int.subNatNat_k (Int.natAbs_k b) (Nat.add (Nat.mod m (Int.natAbs_k b)) 1))
    a

/-- `a / b` for kernel reduction. -/
@[expose] protected noncomputable def ediv_k (a b : Int) : Int :=
  Int.rec
    (fun m => Int.rec (fun n => Int.ofNat (Nat.div m n)) (fun n => Int.negOfNat_k (Nat.div m (Nat.add n 1))) b)
    (fun m => Int.rec (fun n => Bool.rec (Int.negSucc (Nat.div m n)) (Int.ofNat 0) (Nat.beq n 0))
      (fun n => Int.ofNat (Nat.add (Nat.div m (Nat.add n 1)) 1)) b)
    a

/-- `a.gcd b` for kernel reduction. -/
@[expose] protected noncomputable def gcd_k (a b : Int) : Nat :=
  Nat.gcd (Int.natAbs_k a) (Int.natAbs_k b)

/-- `a.lcm b` for kernel reduction. -/
@[expose] protected noncomputable def lcm_k (a b : Int) : Nat :=
  Nat.lcm (Int.natAbs_k a) (Int.natAbs_k b)

/-- `x.bmod m` for kernel reduction. -/
@[expose] protected noncomputable def bmod_k (x : Int) (m : Nat) : Int :=
  let r := Int.emod_k x (Int.ofNat m)
  Bool.rec (Int.sub_k r (Int.ofNat m)) r (Int.blt' r (Int.ofNat (Nat.div (Nat.add m 1) 2)))

/-- `a.toNat` for kernel reduction. -/
@[expose] protected noncomputable def toNat_k (a : Int) : Nat :=
  Int.rec (fun m => m) (fun _ => 0) a

/-- `a ^ n` for kernel reduction. -/
@[expose] protected noncomputable def pow_k (a : Int) (n : Nat) : Int :=
  Int.rec (fun m => Int.ofNat (Nat.pow m n))
    (fun m => Bool.rec (Int.negOfNat_k (Nat.pow (Nat.add m 1) n)) (Int.ofNat (Nat.pow (Nat.add m 1) n))
      (Nat.beq (Nat.mod n 2) 0))
    a

theorem subNatNat_k_eq (m n : Nat) : Int.subNatNat_k m n = Int.subNatNat m n := by
  unfold Int.subNatNat_k Int.subNatNat
  cases h : Nat.ble n m with
  | false =>
    have hlt : m < n := Nat.gt_of_not_le (fun h' => nomatch h.symm.trans (Nat.ble_eq.mpr h'))
    have : n - m = (n - m - 1) + 1 := (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hlt)).symm
    simp only; rw [this]; rfl
  | true =>
    have : n - m = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_ble_eq_true h)
    simp only; rw [this]; rfl

theorem negOfNat_k_eq (k : Nat) : Int.negOfNat_k k = Int.negOfNat k := by
  cases k <;> rfl

@[simp] theorem neg_k_eq (a : Int) : Int.neg_k a = Int.neg a := by
  cases a <;> simp only [Int.neg_k, negOfNat_k_eq] <;> rfl

@[simp] theorem add_k_eq (a b : Int) : Int.add_k a b = Int.add a b := by
  cases a <;> cases b <;> simp only [Int.add_k, subNatNat_k_eq] <;> rfl

@[simp] theorem mul_k_eq (a b : Int) : Int.mul_k a b = Int.mul a b := by
  cases a <;> cases b <;> simp only [Int.mul_k, negOfNat_k_eq] <;> rfl

@[simp] theorem natAbs_k_eq (a : Int) : Int.natAbs_k a = a.natAbs := by
  cases a <;> rfl

@[simp] theorem beqZero_k_eq (a : Int) : Int.beqZero_k a = (a == 0) := by
  cases a with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

@[simp] theorem bneZero_k_eq (a : Int) : Int.bneZero_k a = (a != 0) := by
  cases a with
  | ofNat m => cases m <;> rfl
  | negSucc m => rfl

@[simp] theorem emod_k_eq (a b : Int) : Int.emod_k a b = a % b := by
  cases a <;> simp only [Int.emod_k, natAbs_k_eq, subNatNat_k_eq] <;> rfl

@[simp] theorem ediv_k_eq (a b : Int) : Int.ediv_k a b = a / b := by
  cases a <;> cases b
  case negSucc.ofNat m n => cases n <;> rfl
  all_goals simp only [Int.ediv_k, negOfNat_k_eq] <;> rfl

@[simp] theorem sub_k_eq (a b : Int) : Int.sub_k a b = a - b := by
  simp only [Int.sub_k, add_k_eq, neg_k_eq]; rfl

@[simp] theorem gcd_k_eq (a b : Int) : Int.gcd_k a b = a.gcd b := by
  simp only [Int.gcd_k, natAbs_k_eq]; rfl

@[simp] theorem lcm_k_eq (a b : Int) : Int.lcm_k a b = a.lcm b := by
  simp only [Int.lcm_k, natAbs_k_eq]; rfl

@[simp] theorem bmod_k_eq (x : Int) (m : Nat) : Int.bmod_k x m = x.bmod m := by
  have hm : Int.ofNat (Nat.div (Nat.add m 1) 2) = ((m : Int) + 1) / 2 := natCast_ediv (m + 1) 2
  simp only [Int.bmod_k, Int.bmod, emod_k_eq, sub_k_eq, hm, ofNat_eq_natCast]
  cases hb : Int.blt' (x % m) ((m + 1) / 2)
  · have hc : ¬ x % m < (m + 1) / 2 := by rw [← blt'_eq_false]; exact hb
    simp only [hc, ↓reduceIte]
  · have hc : x % m < (m + 1) / 2 := by rw [← blt'_eq_true]; exact hb
    simp only [hc, ↓reduceIte]

@[simp] theorem toNat_k_eq (a : Int) : Int.toNat_k a = a.toNat := by
  cases a <;> rfl

@[simp] theorem pow_k_eq (a : Int) (n : Nat) : Int.pow_k a n = a ^ n := by
  show Int.pow_k a n = Int.pow a n
  cases a with
  | ofNat m => rfl
  | negSucc m =>
    unfold Int.pow_k Int.pow
    cases h : Nat.beq (Nat.mod n 2) 0
    · have : ¬ n % 2 = 0 := Nat.ne_of_beq_eq_false h
      simp only [this, negOfNat_k_eq, ↓reduceIte]; rfl
    · have : n % 2 = 0 := Nat.eq_of_beq_eq_true h
      simp only [this, ↓reduceIte]; rfl

end Int
