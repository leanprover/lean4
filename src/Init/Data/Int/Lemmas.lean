/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.Int.Basic
import Init.Conv
import Init.NotationExtra
import Init.PropLemmas

namespace Int

open Nat

/-! ## Definitions of basic functions -/

theorem subNatNat_of_sub_eq_zero {m n : Nat} (h : n - m = 0) : subNatNat m n = ↑(m - n) := by
  rw [subNatNat, h, ofNat_eq_coe]

theorem subNatNat_of_sub_eq_succ {m n k : Nat} (h : n - m = succ k) : subNatNat m n = -[k+1] := by
  rw [subNatNat, h]

@[simp] protected theorem neg_zero : -(0:Int) = 0 := rfl

@[norm_cast] theorem ofNat_add (n m : Nat) : (↑(n + m) : Int) = n + m := rfl
@[norm_cast] theorem ofNat_mul (n m : Nat) : (↑(n * m) : Int) = n * m := rfl
theorem ofNat_succ (n : Nat) : (succ n : Int) = n + 1 := rfl

@[local simp] theorem neg_ofNat_zero : -((0 : Nat) : Int) = 0 := rfl
@[local simp] theorem neg_ofNat_succ (n : Nat) : -(succ n : Int) = -[n+1] := rfl
@[local simp] theorem neg_negSucc (n : Nat) : -(-[n+1]) = succ n := rfl

theorem negSucc_coe (n : Nat) : -[n+1] = -↑(n + 1) := rfl

theorem negOfNat_eq : negOfNat n = -ofNat n := rfl

/-! ## These are only for internal use -/

@[simp] theorem add_def {a b : Int} : Int.add a b = a + b := rfl

@[local simp] theorem ofNat_add_ofNat (m n : Nat) : (↑m + ↑n : Int) = ↑(m + n) := rfl
@[local simp] theorem ofNat_add_negSucc (m n : Nat) : ↑m + -[n+1] = subNatNat m (succ n) := rfl
@[local simp] theorem negSucc_add_ofNat (m n : Nat) : -[m+1] + ↑n = subNatNat n (succ m) := rfl
@[local simp] theorem negSucc_add_negSucc (m n : Nat) : -[m+1] + -[n+1] = -[succ (m + n) +1] := rfl

@[simp] theorem mul_def {a b : Int} : Int.mul a b = a * b := rfl

@[local simp] theorem ofNat_mul_ofNat (m n : Nat) : (↑m * ↑n : Int) = ↑(m * n) := rfl
@[local simp] theorem ofNat_mul_negSucc' (m n : Nat) : ↑m * -[n+1] = negOfNat (m * succ n) := rfl
@[local simp] theorem negSucc_mul_ofNat' (m n : Nat) : -[m+1] * ↑n = negOfNat (succ m * n) := rfl
@[local simp] theorem negSucc_mul_negSucc' (m n : Nat) :
    -[m+1] * -[n+1] = ofNat (succ m * succ n) := rfl

/- ## some basic functions and properties -/

@[norm_cast] theorem ofNat_inj : ((m : Nat) : Int) = (n : Nat) ↔ m = n := ⟨ofNat.inj, congrArg _⟩

theorem ofNat_eq_zero : ((n : Nat) : Int) = 0 ↔ n = 0 := ofNat_inj

theorem ofNat_ne_zero : ((n : Nat) : Int) ≠ 0 ↔ n ≠ 0 := not_congr ofNat_eq_zero

theorem negSucc_inj : negSucc m = negSucc n ↔ m = n := ⟨negSucc.inj, fun H => by simp [H]⟩

theorem negSucc_eq (n : Nat) : -[n+1] = -((n : Int) + 1) := rfl

@[simp] theorem negSucc_ne_zero (n : Nat) : -[n+1] ≠ 0 := nofun

@[simp] theorem zero_ne_negSucc (n : Nat) : 0 ≠ -[n+1] := nofun

@[simp, norm_cast] theorem Nat.cast_ofNat_Int :
  (Nat.cast (no_index (OfNat.ofNat n)) : Int) = OfNat.ofNat n := rfl

/- ## neg -/

@[simp] protected theorem neg_neg : ∀ a : Int, -(-a) = a
  | 0      => rfl
  | succ _ => rfl
  | -[_+1] => rfl

@[simp] protected theorem neg_inj {a b : Int} : -a = -b ↔ a = b :=
  ⟨fun h => by rw [← Int.neg_neg a, ← Int.neg_neg b, h], congrArg _⟩

@[simp] protected theorem neg_eq_zero : -a = 0 ↔ a = 0 := Int.neg_inj (b := 0)

protected theorem neg_ne_zero : -a ≠ 0 ↔ a ≠ 0 := not_congr Int.neg_eq_zero

protected theorem sub_eq_add_neg {a b : Int} : a - b = a + -b := rfl

theorem add_neg_one (i : Int) : i + -1 = i - 1 := rfl

/- ## basic properties of subNatNat -/

@[elab_as_elim]
theorem subNatNat_elim (m n : Nat) (motive : Nat → Nat → Int → Prop)
    (hp : ∀ i n, motive (n + i) n i)
    (hn : ∀ i m, motive m (m + i + 1) -[i+1]) :
    motive m n (subNatNat m n) := by
  unfold subNatNat
  match h : n - m with
  | 0 =>
    have ⟨k, h⟩ := Nat.le.dest (Nat.le_of_sub_eq_zero h)
    rw [h.symm, Nat.add_sub_cancel_left]; apply hp
  | succ k =>
    rw [Nat.sub_eq_iff_eq_add (Nat.le_of_lt (Nat.lt_of_sub_eq_succ h))] at h
    rw [h, Nat.add_comm]; apply hn

theorem subNatNat_add_left : subNatNat (m + n) m = n := by
  unfold subNatNat
  rw [Nat.sub_eq_zero_of_le (Nat.le_add_right ..), Nat.add_sub_cancel_left, ofNat_eq_coe]

theorem subNatNat_add_right : subNatNat m (m + n + 1) = negSucc n := by
  simp [subNatNat, Nat.add_assoc, Nat.add_sub_cancel_left]

theorem subNatNat_add_add (m n k : Nat) : subNatNat (m + k) (n + k) = subNatNat m n := by
  apply subNatNat_elim m n (fun m n i => subNatNat (m + k) (n + k) = i)
  focus
    intro i j
    rw [Nat.add_assoc, Nat.add_comm i k, ← Nat.add_assoc]
    exact subNatNat_add_left
  focus
    intro i j
    rw [Nat.add_assoc j i 1, Nat.add_comm j (i+1), Nat.add_assoc, Nat.add_comm (i+1) (j+k)]
    exact subNatNat_add_right

theorem subNatNat_of_le {m n : Nat} (h : n ≤ m) : subNatNat m n = ↑(m - n) :=
  subNatNat_of_sub_eq_zero (Nat.sub_eq_zero_of_le h)

theorem subNatNat_of_lt {m n : Nat} (h : m < n) : subNatNat m n = -[pred (n - m) +1] :=
  subNatNat_of_sub_eq_succ <| (Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)).symm

@[simp] theorem subNat_eq_zero_iff {a b : Nat} : subNatNat a b = 0 ↔ a = b := by
  cases Nat.lt_or_ge a b with
  | inl h =>
    rw [subNatNat_of_lt h]
    simpa using ne_of_lt h
  | inr h =>
    rw [subNatNat_of_le h]
    norm_cast
    rw [Nat.sub_eq_iff_eq_add' h]
    simp

/- # Additive group properties -/

/- addition -/

protected theorem add_comm : ∀ a b : Int, a + b = b + a
  | ofNat n, ofNat m => by simp [Nat.add_comm]
  | ofNat _, -[_+1]  => rfl
  | -[_+1],  ofNat _ => rfl
  | -[_+1],  -[_+1]  => by simp [Nat.add_comm]
instance : Std.Commutative (α := Int) (· + ·) := ⟨Int.add_comm⟩

@[simp] protected theorem add_zero : ∀ a : Int, a + 0 = a
  | ofNat _ => rfl
  | -[_+1]  => rfl

@[simp] protected theorem zero_add (a : Int) : 0 + a = a := Int.add_comm .. ▸ a.add_zero
instance : Std.LawfulIdentity (α := Int) (· + ·) 0 where
  left_id := Int.zero_add
  right_id := Int.add_zero

theorem ofNat_add_negSucc_of_lt (h : m < n.succ) : ofNat m + -[n+1] = -[n - m+1] :=
  show subNatNat .. = _ by simp [succ_sub (le_of_lt_succ h), subNatNat]

theorem subNatNat_sub (h : n ≤ m) (k : Nat) : subNatNat (m - n) k = subNatNat m (k + n) := by
  rwa [← subNatNat_add_add _ _ n, Nat.sub_add_cancel]

theorem subNatNat_add (m n k : Nat) : subNatNat (m + n) k = m + subNatNat n k := by
  cases n.lt_or_ge k with
  | inl h' =>
    simp [subNatNat_of_lt h', sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt h')]
    conv => lhs; rw [← Nat.sub_add_cancel (Nat.le_of_lt h')]
    apply subNatNat_add_add
  | inr h' => simp [subNatNat_of_le h',
      subNatNat_of_le (Nat.le_trans h' (le_add_left ..)), Nat.add_sub_assoc h']

theorem subNatNat_add_negSucc (m n k : Nat) :
    subNatNat m n + -[k+1] = subNatNat m (n + succ k) := by
  have h := Nat.lt_or_ge m n
  cases h with
  | inr h' =>
    rw [subNatNat_of_le h']
    simp
    rw [subNatNat_sub h', Nat.add_comm]
  | inl h' =>
    have h₂ : m < n + succ k := Nat.lt_of_lt_of_le h' (le_add_right _ _)
    rw [subNatNat_of_lt h', subNatNat_of_lt h₂]
    simp only [pred_eq_sub_one, negSucc_add_negSucc, succ_eq_add_one, negSucc.injEq]
    rw [Nat.add_right_comm, sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt h'), Nat.sub_sub,
      ← Nat.add_assoc, succ_sub_succ_eq_sub, Nat.add_comm n,Nat.add_sub_assoc (Nat.le_of_lt h'),
      Nat.add_comm]

protected theorem add_assoc : ∀ a b c : Int, a + b + c = a + (b + c)
  | (m:Nat), (n:Nat), _ => aux1 ..
  | Nat.cast m, b, Nat.cast k => by
    rw [Int.add_comm, ← aux1, Int.add_comm k, aux1, Int.add_comm b]
  | a, (n:Nat), (k:Nat) => by
    rw [Int.add_comm, Int.add_comm a, ← aux1, Int.add_comm a, Int.add_comm k]
  | -[_+1], -[_+1], (k:Nat) => aux2 ..
  | -[m+1], (n:Nat), -[k+1] => by
    rw [Int.add_comm, ← aux2, Int.add_comm n, ← aux2, Int.add_comm -[m+1]]
  | (m:Nat), -[n+1], -[k+1] => by
    rw [Int.add_comm, Int.add_comm m, Int.add_comm m, ← aux2, Int.add_comm -[k+1]]
  | -[m+1], -[n+1], -[k+1] => by
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
where
  aux1 (m n : Nat) : ∀ c : Int, m + n + c = m + (n + c)
    | (k:Nat) => by simp [Nat.add_assoc]
    | -[k+1]  => by simp [subNatNat_add]
  aux2 (m n k : Nat) : -[m+1] + -[n+1] + k = -[m+1] + (-[n+1] + k) := by
    simp
    rw [Int.add_comm, subNatNat_add_negSucc]
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
instance : Std.Associative (α := Int) (· + ·) := ⟨Int.add_assoc⟩

protected theorem add_left_comm (a b c : Int) : a + (b + c) = b + (a + c) := by
  rw [← Int.add_assoc, Int.add_comm a, Int.add_assoc]

protected theorem add_right_comm (a b c : Int) : a + b + c = a + c + b := by
  rw [Int.add_assoc, Int.add_comm b, ← Int.add_assoc]

/- ## negation -/

theorem subNatNat_self : ∀ n, subNatNat n n = 0
  | 0      => rfl
  | succ m => by rw [subNatNat_of_sub_eq_zero (Nat.sub_self ..), Nat.sub_self, ofNat_zero]

attribute [local simp] subNatNat_self

@[local simp] protected theorem add_left_neg : ∀ a : Int, -a + a = 0
  | 0      => rfl
  | succ m => by simp
  | -[m+1] => by simp

@[local simp] protected theorem add_right_neg (a : Int) : a + -a = 0 := by
  rw [Int.add_comm, Int.add_left_neg]

protected theorem neg_eq_of_add_eq_zero {a b : Int} (h : a + b = 0) : -a = b := by
  rw [← Int.add_zero (-a), ← h, ← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem eq_neg_of_eq_neg {a b : Int} (h : a = -b) : b = -a := by
  rw [h, Int.neg_neg]

protected theorem eq_neg_comm {a b : Int} : a = -b ↔ b = -a :=
  ⟨Int.eq_neg_of_eq_neg, Int.eq_neg_of_eq_neg⟩

protected theorem neg_eq_comm {a b : Int} : -a = b ↔ -b = a := by
  rw [eq_comm, Int.eq_neg_comm, eq_comm]

protected theorem neg_add_cancel_left (a b : Int) : -a + (a + b) = b := by
  rw [← Int.add_assoc, Int.add_left_neg, Int.zero_add]

protected theorem add_neg_cancel_left (a b : Int) : a + (-a + b) = b := by
  rw [← Int.add_assoc, Int.add_right_neg, Int.zero_add]

protected theorem add_neg_cancel_right (a b : Int) : a + b + -b = a := by
  rw [Int.add_assoc, Int.add_right_neg, Int.add_zero]

protected theorem neg_add_cancel_right (a b : Int) : a + -b + b = a := by
  rw [Int.add_assoc, Int.add_left_neg, Int.add_zero]

protected theorem add_left_cancel {a b c : Int} (h : a + b = a + c) : b = c := by
  have h₁ : -a + (a + b) = -a + (a + c) := by rw [h]
  simp [← Int.add_assoc, Int.add_left_neg, Int.zero_add] at h₁; exact h₁

@[local simp] protected theorem neg_add {a b : Int} : -(a + b) = -a + -b := by
  apply Int.add_left_cancel (a := a + b)
  rw [Int.add_right_neg, Int.add_comm a, ← Int.add_assoc, Int.add_assoc b,
    Int.add_right_neg, Int.add_zero, Int.add_right_neg]

/--
If a predicate on the integers is invariant under negation,
then it is sufficient to prove it for the nonnegative integers.
-/
theorem wlog_sign {P : Int → Prop} (inv : ∀ a, P a ↔ P (-a)) (w : ∀ n : Nat, P n) (a : Int) : P a := by
  cases a with
  | ofNat n => exact w n
  | negSucc n =>
    rw [negSucc_eq, ← inv, ← ofNat_succ]
    apply w

/- ## subtraction -/

@[simp] theorem negSucc_sub_one (n : Nat) : -[n+1] - 1 = -[n + 1 +1] := rfl

@[simp] protected theorem sub_self (a : Int) : a - a = 0 := by
  rw [Int.sub_eq_add_neg, Int.add_right_neg]

@[simp] protected theorem sub_zero (a : Int) : a - 0 = a := by simp [Int.sub_eq_add_neg]

@[simp] protected theorem zero_sub (a : Int) : 0 - a = -a := by simp [Int.sub_eq_add_neg]

protected theorem sub_eq_zero_of_eq {a b : Int} (h : a = b) : a - b = 0 := by
  rw [h, Int.sub_self]

protected theorem eq_of_sub_eq_zero {a b : Int} (h : a - b = 0) : a = b := by
  have : 0 + b = b := by rw [Int.zero_add]
  have : a - b + b = b := by rwa [h]
  rwa [Int.sub_eq_add_neg, Int.neg_add_cancel_right] at this

protected theorem sub_eq_zero {a b : Int} : a - b = 0 ↔ a = b :=
  ⟨Int.eq_of_sub_eq_zero, Int.sub_eq_zero_of_eq⟩

protected theorem sub_sub (a b c : Int) : a - b - c = a - (b + c) := by
  simp [Int.sub_eq_add_neg, Int.add_assoc]

protected theorem neg_sub (a b : Int) : -(a - b) = b - a := by
  simp [Int.sub_eq_add_neg, Int.add_comm]

protected theorem sub_sub_self (a b : Int) : a - (a - b) = b := by
  simp [Int.sub_eq_add_neg, ← Int.add_assoc]

@[simp] protected theorem sub_neg (a b : Int) : a - -b = a + b := by simp [Int.sub_eq_add_neg]

@[simp] protected theorem sub_add_cancel (a b : Int) : a - b + b = a :=
  Int.neg_add_cancel_right a b

@[simp] protected theorem add_sub_cancel (a b : Int) : a + b - b = a :=
  Int.add_neg_cancel_right a b

protected theorem add_sub_assoc (a b c : Int) : a + b - c = a + (b - c) := by
  rw [Int.sub_eq_add_neg, Int.add_assoc, ← Int.sub_eq_add_neg]

@[norm_cast] theorem ofNat_sub (h : m ≤ n) : ((n - m : Nat) : Int) = n - m := by
  match m with
  | 0 => rfl
  | succ m =>
    show ofNat (n - succ m) = subNatNat n (succ m)
    rw [subNatNat, Nat.sub_eq_zero_of_le h]

theorem negSucc_coe' (n : Nat) : -[n+1] = -↑n - 1 := by
  rw [Int.sub_eq_add_neg, ← Int.neg_add]; rfl

protected theorem subNatNat_eq_coe {m n : Nat} : subNatNat m n = ↑m - ↑n := by
  apply subNatNat_elim m n fun m n i => i = m - n
  · intros i n
    rw [Int.ofNat_add, Int.sub_eq_add_neg, Int.add_assoc, Int.add_left_comm,
      Int.add_right_neg, Int.add_zero]
  · intros i n
    simp only [negSucc_coe, ofNat_add, Int.sub_eq_add_neg, Int.neg_add, ← Int.add_assoc]
    rw [← @Int.sub_eq_add_neg n, ← ofNat_sub, Nat.sub_self, ofNat_zero, Int.zero_add]
    apply Nat.le_refl

theorem toNat_sub (m n : Nat) : toNat (m - n) = m - n := by
  rw [← Int.subNatNat_eq_coe]
  refine subNatNat_elim m n (fun m n i => toNat i = m - n) (fun i n => ?_) (fun i n => ?_)
  · exact (Nat.add_sub_cancel_left ..).symm
  · dsimp; rw [Nat.add_assoc, Nat.sub_eq_zero_of_le (Nat.le_add_right ..)]; rfl

theorem toNat_of_nonpos : ∀ {z : Int}, z ≤ 0 → z.toNat = 0
  | 0, _ => rfl
  | -[_+1], _ => rfl

@[simp] theorem neg_ofNat_eq_negSucc_iff {a b : Nat} : - (a : Int) = -[b+1] ↔ a = b + 1 := by
  rw [Int.neg_eq_comm]
  rw [Int.neg_negSucc]
  norm_cast
  simp [eq_comm]

@[simp] theorem neg_ofNat_eq_negSucc_add_one_iff {a b : Nat} : - (a : Int) = -[b+1] + 1 ↔ a = b := by
  cases b with
  | zero => simp; norm_cast
  | succ b =>
    rw [Int.neg_eq_comm, ← Int.negSucc_sub_one, Int.sub_add_cancel, Int.neg_negSucc]
    norm_cast
    simp [eq_comm]

/- ## add/sub injectivity -/

protected theorem add_left_inj {i j : Int} (k : Int) : (i + k = j + k) ↔ i = j := by
  apply Iff.intro
  · intro p
    rw [←Int.add_sub_cancel i k, ←Int.add_sub_cancel j k, p]
  · exact congrArg (· + k)

protected theorem add_right_inj {i j : Int} (k : Int) : (k + i = k + j) ↔ i = j := by
  simp [Int.add_comm k, Int.add_left_inj]

protected theorem sub_right_inj {i j : Int} (k : Int) : (k - i = k - j) ↔ i = j := by
  simp [Int.sub_eq_add_neg, Int.neg_inj, Int.add_right_inj]

protected theorem sub_left_inj {i j : Int} (k : Int) : (i - k = j - k) ↔ i = j := by
  simp [Int.sub_eq_add_neg, Int.add_left_inj]

/- ## Ring properties -/

@[simp] theorem ofNat_mul_negSucc (m n : Nat) : (m : Int) * -[n+1] = -↑(m * succ n) := rfl

@[simp] theorem negSucc_mul_ofNat (m n : Nat) : -[m+1] * n = -↑(succ m * n) := rfl

@[simp] theorem negSucc_mul_negSucc (m n : Nat) : -[m+1] * -[n+1] = succ m * succ n := rfl

protected theorem mul_comm (a b : Int) : a * b = b * a := by
  cases a <;> cases b <;> simp [Nat.mul_comm]
instance : Std.Commutative (α := Int) (· * ·) := ⟨Int.mul_comm⟩

theorem ofNat_mul_negOfNat (m n : Nat) : (m : Nat) * negOfNat n = negOfNat (m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_ofNat (m n : Nat) : negOfNat m * (n : Nat) = negOfNat (m * n) := by
  rw [Int.mul_comm]; simp [ofNat_mul_negOfNat, Nat.mul_comm]

theorem negSucc_mul_negOfNat (m n : Nat) : -[m+1] * negOfNat n = ofNat (succ m * n) := by
  cases n <;> rfl

theorem negOfNat_mul_negSucc (m n : Nat) : negOfNat n * -[m+1] = ofNat (n * succ m) := by
  rw [Int.mul_comm, negSucc_mul_negOfNat, Nat.mul_comm]

attribute [local simp] ofNat_mul_negOfNat negOfNat_mul_ofNat
  negSucc_mul_negOfNat negOfNat_mul_negSucc

protected theorem mul_assoc (a b c : Int) : a * b * c = a * (b * c) := by
  cases a <;> cases b <;> cases c <;> simp [Nat.mul_assoc]
instance : Std.Associative (α := Int) (· * ·) := ⟨Int.mul_assoc⟩

protected theorem mul_left_comm (a b c : Int) : a * (b * c) = b * (a * c) := by
  rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm a]

protected theorem mul_right_comm (a b c : Int) : a * b * c = a * c * b := by
  rw [Int.mul_assoc, Int.mul_assoc, Int.mul_comm b]

@[simp] protected theorem mul_zero (a : Int) : a * 0 = 0 := by cases a <;> rfl

@[simp] protected theorem zero_mul (a : Int) : 0 * a = 0 := Int.mul_comm .. ▸ a.mul_zero

theorem negOfNat_eq_subNatNat_zero (n) : negOfNat n = subNatNat 0 n := by cases n <;> rfl

theorem ofNat_mul_subNatNat (m n k : Nat) :
    m * subNatNat n k = subNatNat (m * n) (m * k) := by
  cases m with
  | zero => simp [ofNat_zero, Int.zero_mul, Nat.zero_mul]
  | succ m => cases n.lt_or_ge k with
    | inl h =>
      have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
      simp [subNatNat_of_lt h, subNatNat_of_lt h']
      rw [sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt h), ← neg_ofNat_succ, Nat.mul_sub_left_distrib,
        ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h')]; rfl
    | inr h =>
      have h' : succ m * k ≤ succ m * n := Nat.mul_le_mul_left _ h
      simp [subNatNat_of_le h, subNatNat_of_le h', Nat.mul_sub_left_distrib]

theorem negOfNat_add (m n : Nat) : negOfNat m + negOfNat n = negOfNat (m + n) := by
  cases m <;> cases n <;> simp [Nat.succ_add] <;> rfl

theorem negSucc_mul_subNatNat (m n k : Nat) :
    -[m+1] * subNatNat n k = subNatNat (succ m * k) (succ m * n) := by
  cases n.lt_or_ge k with
  | inl h =>
    have h' : succ m * n < succ m * k := Nat.mul_lt_mul_of_pos_left h (Nat.succ_pos m)
    rw [subNatNat_of_lt h, subNatNat_of_le (Nat.le_of_lt h')]
    simp [sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt h), Nat.mul_sub_left_distrib]
  | inr h => cases Nat.lt_or_ge k n with
    | inl h' =>
      have h₁ : succ m * n > succ m * k := Nat.mul_lt_mul_of_pos_left h' (Nat.succ_pos m)
      rw [subNatNat_of_le h, subNatNat_of_lt h₁, negSucc_mul_ofNat,
        Nat.mul_sub_left_distrib, ← succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁)]; rfl
    | inr h' => rw [Nat.le_antisymm h h', subNatNat_self, subNatNat_self, Int.mul_zero]

attribute [local simp] ofNat_mul_subNatNat negOfNat_add negSucc_mul_subNatNat

protected theorem mul_add : ∀ a b c : Int, a * (b + c) = a * b + a * c
  | (m:Nat), (n:Nat), (k:Nat) => by simp [Nat.left_distrib]
  | (m:Nat), (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  (k:Nat) => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | (m:Nat), -[n+1],  -[k+1]  => by simp [← Nat.left_distrib, Nat.add_left_comm, Nat.add_assoc]
  | -[m+1],  (n:Nat), (k:Nat) => by simp [Nat.mul_comm]; rw [← Nat.right_distrib, Nat.mul_comm]
  | -[m+1],  (n:Nat), -[k+1]  => by
    simp [negOfNat_eq_subNatNat_zero]; rw [Int.add_comm, ← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  (k:Nat) => by simp [negOfNat_eq_subNatNat_zero]; rw [← subNatNat_add]; rfl
  | -[m+1],  -[n+1],  -[k+1]  => by simp [← Nat.left_distrib, Nat.add_left_comm, Nat.add_assoc]

protected theorem add_mul (a b c : Int) : (a + b) * c = a * c + b * c := by
  simp [Int.mul_comm, Int.mul_add]

protected theorem neg_mul_eq_neg_mul (a b : Int) : -(a * b) = -a * b :=
  Int.neg_eq_of_add_eq_zero <| by rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]

protected theorem neg_mul_eq_mul_neg (a b : Int) : -(a * b) = a * -b :=
  Int.neg_eq_of_add_eq_zero <| by rw [← Int.mul_add, Int.add_right_neg, Int.mul_zero]

@[simp] protected theorem neg_mul (a b : Int) : -a * b = -(a * b) :=
  (Int.neg_mul_eq_neg_mul a b).symm

@[simp] protected theorem mul_neg (a b : Int) : a * -b = -(a * b) :=
  (Int.neg_mul_eq_mul_neg a b).symm

protected theorem neg_mul_neg (a b : Int) : -a * -b = a * b := by simp

protected theorem neg_mul_comm (a b : Int) : -a * b = a * -b := by simp

protected theorem mul_sub (a b c : Int) : a * (b - c) = a * b - a * c := by
  simp [Int.sub_eq_add_neg, Int.mul_add]

protected theorem sub_mul (a b c : Int) : (a - b) * c = a * c - b * c := by
  simp [Int.sub_eq_add_neg, Int.add_mul]

@[simp] protected theorem one_mul : ∀ a : Int, 1 * a = a
  | ofNat n => show ofNat (1 * n) = ofNat n by rw [Nat.one_mul]
  | -[n+1]  => show -[1 * n +1] = -[n+1] by rw [Nat.one_mul]

@[simp] protected theorem mul_one (a : Int) : a * 1 = a := by rw [Int.mul_comm, Int.one_mul]
instance : Std.LawfulIdentity (α := Int) (· * ·) 1 where
  left_id := Int.one_mul
  right_id := Int.mul_one

protected theorem mul_neg_one (a : Int) : a * -1 = -a := by rw [Int.mul_neg, Int.mul_one]

protected theorem neg_eq_neg_one_mul : ∀ a : Int, -a = -1 * a
  | 0      => rfl
  | succ n => show _ = -[1 * n +1] by rw [Nat.one_mul]; rfl
  | -[n+1] => show _ = ofNat _ by rw [Nat.one_mul]; rfl

protected theorem mul_eq_zero {a b : Int} : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  refine ⟨fun h => ?_, fun h => h.elim (by simp [·, Int.zero_mul]) (by simp [·, Int.mul_zero])⟩
  exact match a, b, h with
  | .ofNat 0, _, _ => by simp
  | _, .ofNat 0, _ => by simp
  | .ofNat (a+1), .negSucc b, h => by cases h

protected theorem mul_ne_zero {a b : Int} (a0 : a ≠ 0) (b0 : b ≠ 0) : a * b ≠ 0 :=
  Or.rec a0 b0 ∘ Int.mul_eq_zero.mp

@[simp] protected theorem mul_ne_zero_iff {a b : Int} : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  rw [ne_eq, Int.mul_eq_zero, not_or, ne_eq]

protected theorem eq_of_mul_eq_mul_right {a b c : Int} (ha : a ≠ 0) (h : b * a = c * a) : b = c :=
  have : (b - c) * a = 0 := by rwa [Int.sub_mul, Int.sub_eq_zero]
  Int.sub_eq_zero.1 <| (Int.mul_eq_zero.mp this).resolve_right ha

protected theorem eq_of_mul_eq_mul_left {a b c : Int} (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  have : a * b - a * c = 0 := Int.sub_eq_zero_of_eq h
  have : a * (b - c) = 0 := by rw [Int.mul_sub, this]
  have : b - c = 0 := (Int.mul_eq_zero.1 this).resolve_left ha
  Int.eq_of_sub_eq_zero this

theorem mul_eq_mul_left_iff {a b c : Int} (h : c ≠ 0) : c * a = c * b ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_left h, fun w => congrArg (fun x => c * x) w⟩

theorem mul_eq_mul_right_iff {a b c : Int} (h : c ≠ 0) : a * c = b * c ↔ a = b :=
  ⟨Int.eq_of_mul_eq_mul_right h, fun w => congrArg (fun x => x * c) w⟩

theorem eq_one_of_mul_eq_self_left {a b : Int} (Hpos : a ≠ 0) (H : b * a = a) : b = 1 :=
  Int.eq_of_mul_eq_mul_right Hpos <| by rw [Int.one_mul, H]

theorem eq_one_of_mul_eq_self_right {a b : Int} (Hpos : b ≠ 0) (H : b * a = b) : a = 1 :=
  Int.eq_of_mul_eq_mul_left Hpos <| by rw [Int.mul_one, H]

/-! NatCast lemmas -/

/-!
The following lemmas are later subsumed by e.g. `Nat.cast_add` and `Nat.cast_mul` in Mathlib
but it is convenient to have these earlier, for users who only need `Nat` and `Int`.
-/

theorem natCast_zero : ((0 : Nat) : Int) = (0 : Int) := rfl

theorem natCast_one : ((1 : Nat) : Int) = (1 : Int) := rfl

@[simp] theorem natCast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  -- Note this only works because of local simp attributes in this file,
  -- so it still makes sense to tag the lemmas with `@[simp]`.
  simp

@[simp] theorem natCast_mul (a b : Nat) : ((a * b : Nat) : Int) = (a : Int) * (b : Int) := by
  simp

end Int
