/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Packed
public import Init.Grind.Ring.FieldSolver
import Init.Omega
import Init.ByCases
import Init.Data.Int.Order
import Init.Data.Int.LemmasAux
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section

namespace Lean.Grind.CommRing
/-!
Ring identities by Kronecker substitution.

Evaluating a polynomial with integer coefficients at the point `xᵢ = X ^ (B ^ i)` maps the
monomial with packed code `v` to `X ^ v`. When `B` is larger than every degree and `2 * ‖p‖₁ < X`,
two polynomials with the same value are equal: the value written in base `X` has the coefficients
as digits. So the kernel checks an identity `a = b` by evaluating `a` and `b` at the point, which is
arithmetic on large natural numbers that it performs on literals directly, and by bounding the
coefficients with `Expr.majorant_k`. The polynomials of `a` and `b` are not computed: they only
appear in the proof (`Expr.toPP_k`).
-/

open Std
open AddCommMonoid AddCommGroup NatModule IntModule
open Semiring hiding add_zero add_comm add_assoc
open Ring hiding sub_eq_add_neg
open CommSemiring

attribute [local instance] Semiring.natCast Ring.intCast

/-- The value of `p` at the point `xᵢ = X ^ (B ^ i)`, where the monomial with code `v` is `X ^ v`. -/
def PPoly.kron (X : Int) : PPoly → Int
  | .num k => k
  | .add k _ v p => k * X ^ v + kron X p

/-- The coefficient of the monomial with code `c` (the constant has code `0`). -/
def PPoly.coeff (c : Nat) : PPoly → Int
  | .num k => if c = 0 then k else 0
  | .add k _ v p => (if v = c then k else 0) + coeff c p

/-- The sum of the absolute values of the coefficients. -/
def PPoly.norm1 : PPoly → Nat
  | .num k => k.natAbs
  | .add k _ _ p => k.natAbs + norm1 p

def PPoly.size : PPoly → Nat
  | .num _ => 0
  | .add _ _ _ p => size p + 1

/-- `p` without its terms with code `c`. -/
def PPoly.removeCode (c : Nat) : PPoly → PPoly
  | .num k => if c = 0 then .num 0 else .num k
  | .add k d v p => if v = c then removeCode c p else .add k d v (removeCode c p)

/-- `p` without the terms with code `0`, and the other codes decremented. -/
def PPoly.shiftDown : PPoly → PPoly
  | .num _ => .num 0
  | .add k d v p => if v = 0 then shiftDown p else .add k d (v - 1) (shiftDown p)

theorem PPoly.natAbs_coeff_le (c : Nat) (p : PPoly) : (p.coeff c).natAbs ≤ p.norm1 := by
  induction p with
  | num k => simp only [coeff, norm1]; split <;> simp
  | add k d v p ih =>
    simp only [coeff, norm1]
    have := Int.natAbs_add_le (if v = c then k else 0) (p.coeff c)
    split <;> simp at this ⊢ <;> omega

theorem PPoly.norm1_shiftDown_le (p : PPoly) : p.shiftDown.norm1 ≤ p.norm1 := by
  induction p with
  | num k => simp [shiftDown, norm1]
  | add k d v p ih =>
    by_cases h : v = 0
    · simp [shiftDown, norm1, h]; omega
    · simp [shiftDown, norm1, h]; omega

theorem PPoly.coeff_shiftDown (c : Nat) (p : PPoly) : p.shiftDown.coeff c = p.coeff (c + 1) := by
  induction p with
  | num k => simp [shiftDown, coeff]
  | add k d v p ih =>
    by_cases h : v = 0
    · simp [shiftDown, coeff, h, ih]
    · by_cases h' : v = c + 1
      · simp [shiftDown, coeff, h', ih]
      · have : v - 1 ≠ c := by omega
        simp [shiftDown, coeff, h, h', this, ih]

theorem PPoly.kron_shiftDown (X : Int) (p : PPoly) : p.kron X = p.coeff 0 + X * p.shiftDown.kron X := by
  induction p with
  | num k => simp [kron, coeff, shiftDown]
  | add k d v p ih =>
    by_cases h : v = 0
    · subst h
      simp [kron, coeff, shiftDown, ih]
      omega
    · have e : X ^ v = X * X ^ (v - 1) := by
        rw [← Int.pow_succ']; congr 1; omega
      have e' : k * (X * X ^ (v - 1)) = X * (k * X ^ (v - 1)) := by
        rw [← Int.mul_assoc, Int.mul_comm k X, Int.mul_assoc]
      simp [kron, coeff, shiftDown, h, ih, e, e', Int.mul_add]
      omega

/-- The lowest base-`X` digit of the value of `p` is its constant coefficient. -/
theorem PPoly.coeff_zero_of_kron (X : Int) (hX : 0 < X) (p : PPoly) (h : p.kron X = 0) (hn : 2 * (p.norm1 : Int) < X) :
    p.coeff 0 = 0 ∧ p.shiftDown.kron X = 0 := by
  have e := kron_shiftDown X p
  rw [h] at e
  have ha := natAbs_coeff_le 0 p
  have h₁ : p.coeff 0 = -(X * p.shiftDown.kron X) := by omega
  have h₂ : ((p.coeff 0).natAbs : Int) < X := by omega
  rw [h₁, Int.natAbs_neg, Int.natAbs_mul] at h₂
  have hX' : (X.natAbs : Int) = X := Int.natAbs_of_nonneg (Int.le_of_lt hX)
  rcases Nat.eq_zero_or_pos (p.shiftDown.kron X).natAbs with h₃ | h₃
  · have h₃ := Int.natAbs_eq_zero.mp h₃
    exact ⟨by rw [h₁, h₃, Int.mul_zero, Int.neg_zero], h₃⟩
  · have : X.natAbs ≤ X.natAbs * (p.shiftDown.kron X).natAbs := Nat.le_mul_of_pos_right _ h₃
    have : (X.natAbs : Int) ≤ ((X.natAbs * (p.shiftDown.kron X).natAbs : Nat) : Int) := Int.ofNat_le.mpr this
    omega

/-- Base-`X` digits: if `2 * ‖p‖₁ < X` and the value of `p` is `0`, every coefficient is `0`. -/
theorem PPoly.coeff_eq_zero_of_kron (X : Int) (hX : 0 < X) (c : Nat) :
    ∀ p : PPoly, p.kron X = 0 → 2 * (p.norm1 : Int) < X → p.coeff c = 0 := by
  induction c with
  | zero => intro p h hn; exact (coeff_zero_of_kron X hX p h hn).1
  | succ c ih =>
    intro p h hn
    have h₀ := coeff_zero_of_kron X hX p h hn
    have hn' := norm1_shiftDown_le p
    rw [← coeff_shiftDown]
    exact ih p.shiftDown h₀.2 (by omega)

theorem PPoly.size_removeCode_le (c : Nat) (p : PPoly) : (p.removeCode c).size ≤ p.size := by
  induction p with
  | num k => by_cases h : c = 0 <;> simp [removeCode, size, h]
  | add k d v p ih => by_cases h : v = c <;> simp [removeCode, size, h] <;> omega

theorem PPoly.coeff_removeCode (c c' : Nat) (p : PPoly) :
    (p.removeCode c).coeff c' = if c' = c then 0 else p.coeff c' := by
  induction p with
  | num k => by_cases h : c = 0 <;> by_cases h' : c' = c <;> by_cases h'' : c' = 0 <;> simp [removeCode, coeff, h, h', h''] <;> omega
  | add k d v p ih =>
    by_cases h : v = c
    · subst h
      by_cases h' : c' = v
      · subst h'; simp only [removeCode, ite_true]; simpa using ih
      · simp [removeCode, coeff, h', Ne.symm h', ih]
    · by_cases h' : c' = c
      · subst h'; simp [removeCode, coeff, h, ih]
      · by_cases h'' : v = c' <;> simp [removeCode, coeff, h, h', h'', ih]

theorem PPoly.denote_removeCode {α} [Ring α] (f : Nat → α) (B c : Nat) (p : PPoly) :
    p.denote f B = (p.coeff c : α) * monDenote f B 0 c + (p.removeCode c).denote f B := by
  induction p with
  | num k =>
    by_cases h : c = 0
    · subst h; simp [denote, coeff, removeCode, monDenote_zero, intCast_zero, mul_one, add_zero]
    · simp [denote, coeff, removeCode, h, intCast_zero, zero_mul, zero_add]
  | add k d v p ih =>
    by_cases h : v = c
    · subst h
      simp only [denote, coeff, removeCode, ite_true, intCast_add]
      rw [ih, right_distrib, add_assoc]
    · simp only [denote, coeff, removeCode, h, ite_false, zero_add]
      rw [ih, add_left_comm]

/-- A polynomial whose coefficients are all `0` denotes `0`, also when it repeats monomials. -/
theorem PPoly.denote_eq_zero_of_coeff {α} [Ring α] (f : Nat → α) (B : Nat) :
    ∀ (n : Nat) (p : PPoly), p.size ≤ n → (∀ c, p.coeff c = 0) → p.denote f B = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hs h
    cases p with
    | num k => have := h 0; simp [coeff] at this; simp [denote, this, intCast_zero]
    | add => simp [size] at hs
  | succ n ih =>
    intro p hs h
    cases p with
    | num k => have := h 0; simp [coeff] at this; simp [denote, this, intCast_zero]
    | add k d v p =>
      rw [denote_removeCode f B v, h v, intCast_zero, zero_mul, zero_add]
      apply ih
      · have := size_removeCode_le v p
        have : ((PPoly.add k d v p).removeCode v).size = (p.removeCode v).size := by simp [removeCode]
        simp [size] at hs; omega
      · intro c'; rw [coeff_removeCode]; split <;> simp [h]

/-- The packed monomial with code `v` at the point `xᵢ = X ^ (B ^ i)`. -/
theorem PPoly.monDenote_kron (X : Int) {B : Nat} (hB : 1 < B) (i v : Nat) :
    monDenote (fun i => X ^ (B ^ i)) B i v = X ^ (B ^ i * v) := by
  induction v using Nat.strongRecOn generalizing i with
  | _ v ih =>
    by_cases h₀ : v = 0
    · subst h₀; rw [monDenote_zero, Nat.mul_zero, Int.pow_zero]
    rw [monDenote_eq _ hB, ih (v / B) (Nat.div_lt_self (by omega) hB), ← Int.pow_mul, ← Int.pow_add]
    congr 1
    rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div]

theorem PPoly.denote_kron (X : Int) {B : Nat} (hB : 1 < B) (p : PPoly) :
    p.denote (fun i => X ^ (B ^ i)) B = p.kron X := by
  induction p with
  | num k => rfl
  | add k d v p ih =>
    show (k : Int) * monDenote _ B 0 v + p.denote _ B = k * X ^ v + p.kron X
    rw [monDenote_kron X hB, ih, Nat.pow_zero, Nat.one_mul]

/-- `p` followed by `q`, without merging. -/
def PPoly.append : PPoly → PPoly → PPoly
  | .num k, q => append.addConst q k
  | .add k d v p, q => .add k d v (append p q)
where
  addConst : PPoly → Int → PPoly
    | .num k', k => .num (k' + k)
    | .add k' d v p, k => .add k' d v (addConst p k)

def PPoly.neg : PPoly → PPoly
  | .num k => .num (-k)
  | .add k d v p => .add (-k) d v (neg p)

theorem PPoly.denote_append {α} [Ring α] (f : Nat → α) (B : Nat) (p q : PPoly) :
    (p.append q).denote f B = p.denote f B + q.denote f B := by
  have hc : ∀ (q : PPoly) (k : Int), (append.addConst q k).denote f B = q.denote f B + k := by
    intro q k
    induction q with
    | num k' => simp [append.addConst, denote, intCast_add]
    | add k' d v q ih => simp [append.addConst, denote, ih, add_assoc]
  induction p with
  | num k => simp [append, denote, hc, add_comm]
  | add k d v p ih => simp [append, denote, ih, add_assoc]

theorem PPoly.kron_append (X : Int) (p q : PPoly) : (p.append q).kron X = p.kron X + q.kron X := by
  have hc : ∀ (q : PPoly) (k : Int), (append.addConst q k).kron X = q.kron X + k := by
    intro q k
    induction q with
    | num k' => simp [append.addConst, kron]
    | add k' d v q ih => simp [append.addConst, kron, ih]; omega
  induction p with
  | num k => simp [append, kron, hc]; omega
  | add k d v p ih => simp [append, kron, ih]; omega

theorem PPoly.norm1_append (p q : PPoly) : (p.append q).norm1 ≤ p.norm1 + q.norm1 := by
  have hc : ∀ (q : PPoly) (k : Int), (append.addConst q k).norm1 ≤ q.norm1 + k.natAbs := by
    intro q k
    induction q with
    | num k' => simp [append.addConst, norm1]; exact Int.natAbs_add_le k' k
    | add k' d v q ih => simp [append.addConst, norm1]; omega
  induction p with
  | num k => simp [append, norm1]; have := hc q k; omega
  | add k d v p ih => simp [append, norm1]; omega

theorem PPoly.denote_neg {α} [Ring α] (f : Nat → α) (B : Nat) (p : PPoly) : p.neg.denote f B = - p.denote f B := by
  induction p with
  | num k => simp [neg, denote, intCast_neg]
  | add k d v p ih => simp [neg, denote, ih, intCast_neg, neg_mul, neg_add]

theorem PPoly.kron_neg (X : Int) (p : PPoly) : p.neg.kron X = - p.kron X := by
  induction p with
  | num k => simp [neg, kron]
  | add k d v p ih => simp [neg, kron, ih, Int.neg_mul]; omega

theorem PPoly.norm1_neg (p : PPoly) : p.neg.norm1 = p.norm1 := by
  induction p with
  | num k => simp [neg, norm1]
  | add k d v p ih => simp [neg, norm1, ih]

/-- `p` and `q` denote the same, if they have the same value at the point and small coefficients. -/
theorem PPoly.denote_eq_of_kron {α} [Ring α] (f : Nat → α) (B : Nat) (X : Int) (hX : 0 < X) (p q : PPoly)
    (h : p.kron X = q.kron X) (hn : 2 * ((p.norm1 + q.norm1 : Nat) : Int) < X) : p.denote f B = q.denote f B := by
  have hk : (p.append q.neg).kron X = 0 := by rw [kron_append, kron_neg, h]; omega
  have hn' : 2 * ((p.append q.neg).norm1 : Int) < X := by
    have := norm1_append p q.neg; rw [norm1_neg] at this
    have : ((p.append q.neg).norm1 : Int) ≤ ((p.norm1 + q.norm1 : Nat) : Int) := Int.ofNat_le.mpr this
    omega
  have hz := denote_eq_zero_of_coeff f B _ _ (Nat.le_refl _) (fun c => coeff_eq_zero_of_kron X hX c _ hk hn')
  rw [denote_append, denote_neg] at hz
  rw [← sub_eq_zero_iff, sub_eq_add_neg, hz]

/-! Bounds on the coefficients of the polynomials of `Expr.toPP_k`. -/

theorem PPoly.norm1_addConst_k (p : PPoly) (k : Int) : (p.addConst_k k).norm1 ≤ p.norm1 + k.natAbs := by
  unfold addConst_k
  cases h : Int.beqZero_k k
  · dsimp only
    induction p with
    | num k' => show (Int.add_k k' k).natAbs ≤ _; rw [Int.add_k_eq]; exact Int.natAbs_add_le k' k
    | add k' d v p ih => show k'.natAbs + _ ≤ k'.natAbs + _ + _; omega
  · dsimp only; omega

theorem PPoly.norm1_combine_k (p₁ p₂ : PPoly) : (p₁.combine_k p₂).norm1 ≤ p₁.norm1 + p₂.norm1 := by
  induction p₁ generalizing p₂ with
  | num k₁ =>
    have := norm1_addConst_k p₂ k₁
    show (p₂.addConst_k k₁).norm1 ≤ _
    simp only [norm1] at this ⊢; omega
  | add k₁ d₁ v₁ p₁ ih₁ =>
    induction p₂ with
    | num k₂ =>
      have := norm1_addConst_k (.add k₁ d₁ v₁ p₁) k₂
      show ((PPoly.add k₁ d₁ v₁ p₁).addConst_k k₂).norm1 ≤ _
      simp only [norm1] at this ⊢; omega
    | add k₂ d₂ v₂ p₂ ih₂ =>
      have e : (PPoly.add k₁ d₁ v₁ p₁).combine_k (.add k₂ d₂ v₂ p₂) =
          Bool.rec (motive := fun _ => PPoly)
            (Bool.rec (.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))) (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)) (Nat.blt d₁ d₂))
            (Bool.rec
              (Bool.rec (.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)) (.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))) (Nat.blt v₁ v₂))
              (Bool.rec (.add (Int.add_k k₁ k₂) d₁ v₁ (p₁.combine_k p₂)) (p₁.combine_k p₂) (Int.beqZero_k (Int.add_k k₁ k₂)))
              (Nat.beq v₁ v₂))
            (Nat.beq d₁ d₂) := rfl
      rw [e]
      have h₁ := ih₁ (.add k₂ d₂ v₂ p₂)
      have h₁' := ih₁ p₂
      have hsnd : (PPoly.add k₂ d₂ v₂ ((PPoly.add k₁ d₁ v₁ p₁).combine_k p₂)).norm1 ≤
          (PPoly.add k₁ d₁ v₁ p₁).norm1 + (PPoly.add k₂ d₂ v₂ p₂).norm1 := by
        simp only [norm1] at ih₂ ⊢; omega
      have hfst : (PPoly.add k₁ d₁ v₁ (p₁.combine_k (.add k₂ d₂ v₂ p₂))).norm1 ≤
          (PPoly.add k₁ d₁ v₁ p₁).norm1 + (PPoly.add k₂ d₂ v₂ p₂).norm1 := by
        simp only [norm1] at h₁ ⊢; omega
      have hadd := Int.natAbs_add_le k₁ k₂
      cases Nat.beq d₁ d₂
      · cases Nat.blt d₁ d₂
        · exact hfst
        · exact hsnd
      · cases Nat.beq v₁ v₂
        · cases Nat.blt v₁ v₂
          · exact hsnd
          · exact hfst
        · cases Int.beqZero_k (Int.add_k k₁ k₂)
          · show (Int.add_k k₁ k₂).natAbs + (p₁.combine_k p₂).norm1 ≤ (k₁.natAbs + p₁.norm1) + (k₂.natAbs + p₂.norm1)
            rw [Int.add_k_eq]
            show (k₁ + k₂).natAbs + _ ≤ _
            omega
          · show (p₁.combine_k p₂).norm1 ≤ (k₁.natAbs + p₁.norm1) + (k₂.natAbs + p₂.norm1)
            omega

theorem PPoly.norm1_mulConst_k (k : Int) (p : PPoly) : (p.mulConst_k k).norm1 ≤ k.natAbs * p.norm1 := by
  unfold mulConst_k
  cases Int.beqZero_k k
  · dsimp only
    induction p with
    | num k' => show (Int.mul_k k k').natAbs ≤ _; rw [Int.mul_k_eq]; show (k * k').natAbs ≤ _; rw [Int.natAbs_mul]; simp [norm1]
    | add k' d v p ih =>
      show (Int.mul_k k k').natAbs + _ ≤ _
      rw [Int.mul_k_eq]; show (k * k').natAbs + _ ≤ _
      rw [Int.natAbs_mul]; simp only [norm1, Nat.mul_add]; omega
  · show (Int.ofNat 0).natAbs ≤ _; simp

theorem PPoly.norm1_mulMon_k (k : Int) (d v : Nat) (p : PPoly) : (p.mulMon_k k d v).norm1 ≤ k.natAbs * p.norm1 := by
  induction p with
  | num k' =>
    unfold mulMon_k; dsimp only
    cases Int.beqZero_k k'
    · show (Int.mul_k k k').natAbs + (Int.ofNat 0).natAbs ≤ _
      rw [Int.mul_k_eq]; show (k * k').natAbs + 0 ≤ _; rw [Int.natAbs_mul]; simp [norm1]
    · show (Int.ofNat 0).natAbs ≤ _; simp
  | add k' d' v' p ih =>
    show (Int.mul_k k k').natAbs + (p.mulMon_k k d v).norm1 ≤ _
    rw [Int.mul_k_eq]; show (k * k').natAbs + _ ≤ _
    rw [Int.natAbs_mul]; simp only [norm1, Nat.mul_add]; omega

def PPoly.norm1List (ps : List PPoly) : Nat :=
  ps.foldr (fun p n => p.norm1 + n) 0

theorem PPoly.norm1_pairs_k (ps : List PPoly) (pend : Option PPoly) :
    norm1List (pairs_k ps pend) ≤ pend.elim 0 (·.norm1) + norm1List ps := by
  induction ps generalizing pend with
  | nil => cases pend <;> simp [pairs_k, norm1List, Option.elim]
  | cons a ps ih =>
    cases pend with
    | none =>
      have := ih (some a)
      show norm1List (pairs_k ps (some a)) ≤ _
      simp [Option.elim, norm1List] at this ⊢; omega
    | some p =>
      have := ih none
      have hc := norm1_combine_k p a
      show (p.combine_k a).norm1 + norm1List (pairs_k ps none) ≤ _
      simp [Option.elim, norm1List] at this ⊢; omega

theorem PPoly.norm1_foldr_k (ps : List PPoly) : (foldr_k ps).norm1 ≤ norm1List ps := by
  induction ps with
  | nil => show (Int.ofNat 0).natAbs ≤ _; simp
  | cons a ps ih =>
    have := norm1_combine_k a (foldr_k ps)
    show (a.combine_k (foldr_k ps)).norm1 ≤ a.norm1 + norm1List ps
    omega

theorem PPoly.norm1_sumGo_k (fuel ps : List PPoly) : (sumGo_k fuel ps).norm1 ≤ norm1List ps := by
  induction fuel generalizing ps with
  | nil => exact norm1_foldr_k ps
  | cons _ fuel ih =>
    cases ps with
    | nil => show (Int.ofNat 0).natAbs ≤ _; simp
    | cons a rest =>
      cases rest with
      | nil => show a.norm1 ≤ a.norm1 + 0; omega
      | cons b rest =>
        have hp := norm1_pairs_k (a :: b :: rest) none
        have := ih (pairs_k (a :: b :: rest) none)
        show (sumGo_k fuel (pairs_k (a :: b :: rest) none)).norm1 ≤ _
        simp [Option.elim] at hp; omega

theorem PPoly.norm1_sumB_k (ps : List PPoly) : (sumB_k ps).norm1 ≤ norm1List ps :=
  norm1_sumGo_k ps ps

theorem PPoly.norm1_mulTerms_k (p₁ p₂ : PPoly) : norm1List (mulTerms_k p₁ p₂) ≤ p₁.norm1 * p₂.norm1 := by
  induction p₁ with
  | num k =>
    have := norm1_mulConst_k k p₂
    show (p₂.mulConst_k k).norm1 + 0 ≤ k.natAbs * p₂.norm1
    omega
  | add k d v p ih =>
    have := norm1_mulMon_k k d v p₂
    show (p₂.mulMon_k k d v).norm1 + norm1List (mulTerms_k p p₂) ≤ (k.natAbs + p.norm1) * p₂.norm1
    rw [Nat.add_mul]; omega

theorem PPoly.norm1_mulB_k (p₁ p₂ : PPoly) : (mulB_k p₁ p₂).norm1 ≤ p₁.norm1 * p₂.norm1 := by
  cases p₁ with
  | num k => exact norm1_mulConst_k k p₂
  | add k₁ d₁ v₁ q₁ =>
    cases p₂ with
    | num k =>
      have := norm1_mulConst_k k (.add k₁ d₁ v₁ q₁)
      show ((PPoly.add k₁ d₁ v₁ q₁).mulConst_k k).norm1 ≤ _
      rw [Nat.mul_comm]; exact this
    | add k₂ d₂ v₂ q₂ =>
      rw [show mulB_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂) = Bool.rec (Bool.rec (sumB_k (mulTerms_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₂ d₂ v₂ q₂) (.add k₁ d₁ v₁ q₁)) (isMon_k (.add k₂ d₂ v₂ q₂)))
        (mulByMon_k (.add k₁ d₁ v₁ q₁) (.add k₂ d₂ v₂ q₂)) (isMon_k (.add k₁ d₁ v₁ q₁)) from rfl]
      cases hm₁ : isMon_k (.add k₁ d₁ v₁ q₁)
      · cases hm₂ : isMon_k (.add k₂ d₂ v₂ q₂)
        · exact Nat.le_trans (norm1_sumB_k _) (norm1_mulTerms_k _ _)
        · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₂
          rw [e]
          have := norm1_mulMon_k k d v (.add k₁ d₁ v₁ q₁)
          show ((PPoly.add k₁ d₁ v₁ q₁).mulMon_k k d v).norm1 ≤ _ * (k.natAbs + (Int.ofNat 0).natAbs)
          rw [show (Int.ofNat 0).natAbs = 0 from rfl, Nat.add_zero, Nat.mul_comm]; exact this
      · obtain ⟨k, d, v, e⟩ := isMon_k_eq _ hm₁
        rw [e]
        have := norm1_mulMon_k k d v (.add k₂ d₂ v₂ q₂)
        show ((PPoly.add k₂ d₂ v₂ q₂).mulMon_k k d v).norm1 ≤ (k.natAbs + (Int.ofNat 0).natAbs) * _
        rw [show (Int.ofNat 0).natAbs = 0 from rfl, Nat.add_zero]; exact this

theorem PPoly.norm1_powB_k (p : PPoly) (k : Nat) : (powB_k p k).norm1 ≤ p.norm1 ^ k := by
  induction k with
  | zero => show (Int.ofNat 1).natAbs ≤ _; simp
  | succ k ih =>
    rw [show powB_k p (k + 1) = Bool.rec (p.mulB_k (powB_k p k)) p (Nat.beq k 0) from rfl]
    cases hk : Nat.beq k 0
    · have := norm1_mulB_k p (powB_k p k)
      show (p.mulB_k (powB_k p k)).norm1 ≤ _
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.le_trans this (Nat.mul_le_mul_left _ ih)
    · have : k = 0 := Nat.eq_of_beq_eq_true hk
      subst this; show p.norm1 ≤ _; simp

/-- An upper bound on `‖p‖₁` for the polynomial `p` of `e`: the value of `e` with the absolute values of its numerals at `1`. -/
noncomputable def Expr.majorant_k (e : Expr) : Nat :=
  Expr.rec (fun k => Int.natAbs_k k) (fun k => k) (fun k => Int.natAbs_k k) (fun _ => 1) (fun _ ih => ih)
    (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂) (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂) (fun _ _ ih₁ ih₂ => Nat.mul ih₁ ih₂)
    (fun _ k ih => Nat.pow ih k) e

theorem Expr.norm1_powPP_k (B : Nat) (a : Expr) (k : Nat) (p : PPoly) (hp : p.norm1 ≤ a.majorant_k) :
    (a.powPP_k B k p).norm1 ≤ a.majorant_k ^ k := by
  unfold powPP_k
  cases hk0 : Nat.beq k 0
  · have hgen : (p.powB_k k).norm1 ≤ a.majorant_k ^ k :=
      Nat.le_trans (PPoly.norm1_powB_k p k) (Nat.pow_le_pow_left hp k)
    dsimp only
    cases a with
    | num n => show (Int.pow_k n k).natAbs ≤ (Int.natAbs_k n) ^ k; rw [Int.pow_k_eq, Int.natAbs_k_eq, Int.natAbs_pow]; exact Nat.le_refl _
    | natCast n => show (Int.ofNat (Nat.pow n k)).natAbs ≤ n ^ k; exact Nat.le_refl _
    | intCast n => show (Int.pow_k n k).natAbs ≤ (Int.natAbs_k n) ^ k; rw [Int.pow_k_eq, Int.natAbs_k_eq, Int.natAbs_pow]; exact Nat.le_refl _
    | var x => show (Int.ofNat 1).natAbs + (Int.ofNat 0).natAbs ≤ 1 ^ k; simp
    | neg _ => exact hgen
    | add _ _ => exact hgen
    | sub _ _ => exact hgen
    | mul _ _ => exact hgen
    | pow _ _ => exact hgen
  · have : k = 0 := Nat.eq_of_beq_eq_true hk0
    subst this; show (Int.ofNat 1).natAbs ≤ _; simp

theorem Expr.norm1_toPPAcc_k (B : Nat) (e : Expr) :
    ∀ acc : PPoly, (e.toPPAcc_k B acc).norm1 ≤ e.majorant_k + acc.norm1 := by
  have e0 : (PPoly.num (Int.ofNat 0)).norm1 = 0 := rfl
  have e1 : (Int.negSucc 0).natAbs = 1 := rfl
  induction e with
  | num k =>
    intro acc; have := PPoly.norm1_addConst_k acc k
    show (acc.addConst_k k).norm1 ≤ Int.natAbs_k k + _; rw [Int.natAbs_k_eq]; omega
  | natCast k =>
    intro acc; have := PPoly.norm1_addConst_k acc (Int.ofNat k)
    rw [show (Int.ofNat k).natAbs = k from rfl] at this
    show (acc.addConst_k (Int.ofNat k)).norm1 ≤ k + _; omega
  | intCast k =>
    intro acc; have := PPoly.norm1_addConst_k acc k
    show (acc.addConst_k k).norm1 ≤ Int.natAbs_k k + _; rw [Int.natAbs_k_eq]; omega
  | var x =>
    intro acc
    have := PPoly.norm1_combine_k (.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))) acc
    rw [toPPAcc_k_var]
    rw [show (PPoly.add (Int.ofNat 1) 1 (Nat.pow B x) (.num (Int.ofNat 0))).norm1 = 1 from rfl] at this
    exact this
  | neg a ih =>
    intro acc
    have h₁ := ih (.num (Int.ofNat 0))
    have h₂ := PPoly.norm1_mulConst_k (Int.negSucc 0) (a.toPPAcc_k B (.num (Int.ofNat 0)))
    have h₃ := PPoly.norm1_combine_k ((a.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    rw [e0, Nat.add_zero] at h₁; rw [e1, Nat.one_mul] at h₂
    rw [toPPAcc_k_neg]
    show _ ≤ a.majorant_k + _; omega
  | add a b iha ihb =>
    intro acc
    have h₁ := ihb acc
    have h₂ := iha (b.toPPAcc_k B acc)
    rw [toPPAcc_k_add]
    show _ ≤ Nat.add a.majorant_k b.majorant_k + _; rw [Nat.add_eq]; omega
  | sub a b iha ihb =>
    intro acc
    have h₁ := ihb (.num (Int.ofNat 0))
    have h₂ := PPoly.norm1_mulConst_k (Int.negSucc 0) (b.toPPAcc_k B (.num (Int.ofNat 0)))
    have h₃ := PPoly.norm1_combine_k ((b.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc
    have h₄ := iha (PPoly.combine_k ((b.toPPAcc_k B (.num (Int.ofNat 0))).mulConst_k (Int.negSucc 0)) acc)
    rw [e0, Nat.add_zero] at h₁; rw [e1, Nat.one_mul] at h₂
    rw [toPPAcc_k_sub]
    show _ ≤ Nat.add a.majorant_k b.majorant_k + _; rw [Nat.add_eq]; omega
  | mul a b iha ihb =>
    intro acc
    have h₁ := iha (.num (Int.ofNat 0))
    have h₂ := ihb (.num (Int.ofNat 0))
    have h₃ := PPoly.norm1_mulB_k (a.toPPAcc_k B (.num (Int.ofNat 0))) (b.toPPAcc_k B (.num (Int.ofNat 0)))
    have h₄ := PPoly.norm1_combine_k (PPoly.mulB_k (a.toPPAcc_k B (.num (Int.ofNat 0))) (b.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    rw [e0, Nat.add_zero] at h₁ h₂
    rw [toPPAcc_k_mul]
    show _ ≤ Nat.mul a.majorant_k b.majorant_k + _
    have := Nat.mul_le_mul h₁ h₂
    rw [Nat.mul_eq]; omega
  | pow a k ih =>
    intro acc
    have h₁ := ih (.num (Int.ofNat 0))
    rw [e0, Nat.add_zero] at h₁
    have h₂ := Expr.norm1_powPP_k B a k (a.toPPAcc_k B (.num (Int.ofNat 0))) h₁
    have h₃ := PPoly.norm1_combine_k (a.powPP_k B k (a.toPPAcc_k B (.num (Int.ofNat 0)))) acc
    rw [toPPAcc_k_pow]
    show _ ≤ Nat.pow a.majorant_k k + _
    rw [Nat.pow_eq]; omega

/-- The value of `e` at the point `xᵢ = (2 ^ K) ^ (B ^ i)`. -/
noncomputable def Expr.kronEval_k (K B : Nat) (e : Expr) : Int :=
  Expr.rec (fun k => k) (fun n => Int.ofNat n) (fun k => k)
    (fun i => Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.pow B i))))
    (fun _ ih => Int.neg_k ih) (fun _ _ ih₁ ih₂ => Int.add_k ih₁ ih₂) (fun _ _ ih₁ ih₂ => Int.sub_k ih₁ ih₂)
    (fun _ _ ih₁ ih₂ => Int.mul_k ih₁ ih₂) (fun _ k ih => Int.pow_k ih k) e

theorem Expr.kronEval_k_eq (K B : Nat) (e : Expr) :
    e.kronEval_k K B = e.denoteF (fun i => ((2 : Int) ^ K) ^ (B ^ i)) := by
  induction e with
  | num k => show k = denoteInt k; rw [denoteInt_eq]; rfl
  | natCast n => rfl
  | intCast k => rfl
  | var i =>
    show Int.ofNat (2 ^ (K * B ^ i)) = ((2 : Int) ^ K) ^ (B ^ i)
    rw [← Int.pow_mul]; exact Int.natCast_pow 2 (K * B ^ i)
  | neg a ih =>
    show Int.neg_k (a.kronEval_k K B) = - a.denoteF _; rw [Int.neg_k_eq, ih]; rfl
  | add a b iha ihb =>
    show Int.add_k (a.kronEval_k K B) (b.kronEval_k K B) = a.denoteF _ + b.denoteF _; rw [Int.add_k_eq, iha, ihb]; rfl
  | sub a b iha ihb =>
    show Int.sub_k (a.kronEval_k K B) (b.kronEval_k K B) = a.denoteF _ - b.denoteF _; rw [Int.sub_k_eq, iha, ihb]
  | mul a b iha ihb =>
    show Int.mul_k (a.kronEval_k K B) (b.kronEval_k K B) = a.denoteF _ * b.denoteF _; rw [Int.mul_k_eq, iha, ihb]; rfl
  | pow a k ih => show Int.pow_k (a.kronEval_k K B) k = a.denoteF _ ^ k; rw [Int.pow_k_eq, ih]

/-- Checks that `2 ^ K` is larger than twice the coefficients of `a` and `b`. -/
noncomputable def Expr.kronOk_k (K : Nat) (a b : Expr) : Bool :=
  Nat.blt (Nat.mul 2 (Nat.add a.majorant_k b.majorant_k)) (Nat.pow 2 K)

theorem Expr.eq_of_kron {α} [CommRing α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hB : degOk_k B a b = true) (hK : kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) :
    a.denote ctx = b.denote ctx := by
  have hB := of_degOk_k hB
  have hK : 2 * (a.majorant_k + b.majorant_k) < 2 ^ K := Nat.blt_eq.mp hK
  rw [Expr.denote_eq_denoteF, Expr.denote_eq_denoteF, ← denote_toPP_k (Var.denote ctx) B hB.1 a hB.2.1,
    ← denote_toPP_k (Var.denote ctx) B hB.1 b hB.2.2]
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  apply PPoly.denote_eq_of_kron _ B ((2 : Int) ^ K) hX
  · rw [← PPoly.denote_kron _ hB.1, ← PPoly.denote_kron _ hB.1, denote_toPP_k _ B hB.1 a hB.2.1,
      denote_toPP_k _ B hB.1 b hB.2.2, ← kronEval_k_eq, ← kronEval_k_eq, h]
  · have ha := norm1_toPPAcc_k B a (.num (Int.ofNat 0))
    have hb := norm1_toPPAcc_k B b (.num (Int.ofNat 0))
    rw [show (PPoly.num (Int.ofNat 0)).norm1 = 0 from rfl, Nat.add_zero] at ha hb
    have : 2 * ((a.toPP_k B).norm1 + (b.toPP_k B).norm1) < 2 ^ K := by
      unfold toPP_k; omega
    have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
    rw [← h2]
    exact Int.ofNat_lt.mpr (by simpa using this)

theorem eq_true_of_kron {α} [CommRing α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hB : Expr.degOk_k B a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) :
    (a.denote ctx = b.denote ctx) = True :=
  eq_true (Expr.eq_of_kron ctx K B a b hB hK h)

theorem le_true_of_kron {α} [CommRing α] [LE α] [IsPreorder α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hB : Expr.degOk_k B a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) :
    (a.denote ctx ≤ b.denote ctx) = True := by
  rw [Expr.eq_of_kron ctx K B a b hB hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kron {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α) (K B : Nat)
    (a b : Expr) (hB : Expr.degOk_k B a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) :
    (a.denote ctx < b.denote ctx) = False := by
  rw [Expr.eq_of_kron ctx K B a b hB hK h]; exact eq_false Std.lt_irrefl

theorem Expr.eq_of_kronS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hB : degSOk_k B a b = true) (hK : kronOk_k K a b = true)
    (h : a.kronEval_k K B = b.kronEval_k K B) : a.denoteS ctx = b.denoteS ctx := by
  obtain ⟨hS, hB⟩ := of_degSOk_k hB
  have hS := semi_k_and hS
  apply Ring.OfSemiring.toQ_inj
  rw [← Expr.denoteAsRing_eq, ← Expr.denoteAsRing_eq, ← denote_mapCtx_toQ ctx a hS.1, ← denote_mapCtx_toQ ctx b hS.2]
  exact Expr.eq_of_kron _ K B a b hB hK h

theorem eq_true_of_kronS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hB : Expr.degSOk_k B a b = true) (hK : Expr.kronOk_k K a b = true)
    (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx = b.denoteS ctx) = True :=
  eq_true (Expr.eq_of_kronS ctx K B a b hB hK h)

theorem le_true_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [IsPreorder α] (ctx : Context α) (K B : Nat)
    (a b : Expr) (hB : Expr.degSOk_k B a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx ≤ b.denoteS ctx) = True := by
  rw [Expr.eq_of_kronS ctx K B a b hB hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    (ctx : Context α) (K B : Nat) (a b : Expr) (hB : Expr.degSOk_k B a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx < b.denoteS ctx) = False := by
  rw [Expr.eq_of_kronS ctx K B a b hB hK h]; exact eq_false Std.lt_irrefl

/-!
Semiring relations with a common part `c` of both sides: `a = a' + c` and `b = b' + c` are
checked at the point, and `c` is cancelled, so it is never written as a term of the semiring.
-/

theorem eq_cancel_of_kronS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K B : Nat) (a b a' b' c : Expr)
    (hB₁ : Expr.degSOk_k B a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronEval_k K B = (a'.add c).kronEval_k K B)
    (hB₂ : Expr.degSOk_k B b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronEval_k K B = (b'.add c).kronEval_k K B) :
    (a.denoteS ctx = b.denoteS ctx) = (a'.denoteS ctx = b'.denoteS ctx) := by
  rw [Expr.eq_of_kronS ctx K B a (a'.add c) hB₁ hK₁ h₁, Expr.eq_of_kronS ctx K B b (b'.add c) hB₂ hK₂ h₂]
  exact propext AddRightCancel.add_right_cancel_iff

theorem le_cancel_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [IsPreorder α] [OrderedRing α]
    (ctx : Context α) (K B : Nat) (a b a' b' c : Expr)
    (hB₁ : Expr.degSOk_k B a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronEval_k K B = (a'.add c).kronEval_k K B)
    (hB₂ : Expr.degSOk_k B b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronEval_k K B = (b'.add c).kronEval_k K B) :
    (a.denoteS ctx ≤ b.denoteS ctx) = (a'.denoteS ctx ≤ b'.denoteS ctx) := by
  rw [Expr.eq_of_kronS ctx K B a (a'.add c) hB₁ hK₁ h₁, Expr.eq_of_kronS ctx K B b (b'.add c) hB₂ hK₂ h₂]
  exact propext (OrderedAdd.add_le_left_iff _).symm

theorem lt_cancel_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    [OrderedRing α] (ctx : Context α) (K B : Nat) (a b a' b' c : Expr)
    (hB₁ : Expr.degSOk_k B a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronEval_k K B = (a'.add c).kronEval_k K B)
    (hB₂ : Expr.degSOk_k B b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronEval_k K B = (b'.add c).kronEval_k K B) :
    (a.denoteS ctx < b.denoteS ctx) = (a'.denoteS ctx < b'.denoteS ctx) := by
  rw [Expr.eq_of_kronS ctx K B a (a'.add c) hB₁ hK₁ h₁, Expr.eq_of_kronS ctx K B b (b'.add c) hB₂ hK₂ h₂]
  exact propext (OrderedAdd.add_lt_left_iff _).symm

/-!
Linear identities by evaluation at `xᵢ = X ^ (i + 1)`: when every product has a constant factor
(`Expr.degB_k e ≤ 1`), the monomials are the variables, and their codes can be `i + 1` instead of
`B ^ i`, so the values stay small for many variables (`Expr.eq_of_kronLin`).
-/

/-- `p` with the monomial with code `v` valued at `g v`. -/
def PPoly.denoteG {α} [Ring α] (g : Nat → α) : PPoly → α
  | .num k => k
  | .add k _ v p => k * g v + denoteG g p

theorem PPoly.denoteG_removeCode {α} [Ring α] (g : Nat → α) (hg : g 0 = 1) (c : Nat) (p : PPoly) :
    p.denoteG g = (p.coeff c : α) * g c + (p.removeCode c).denoteG g := by
  induction p with
  | num k =>
    by_cases h : c = 0
    · subst h; simp [denoteG, coeff, removeCode, hg, intCast_zero, mul_one, add_zero]
    · simp [denoteG, coeff, removeCode, h, intCast_zero, zero_mul, zero_add]
  | add k d v p ih =>
    by_cases h : v = c
    · subst h
      simp only [denoteG, coeff, removeCode, ite_true, intCast_add]
      rw [ih, right_distrib, add_assoc]
    · simp only [denoteG, coeff, removeCode, h, ite_false, zero_add]
      rw [ih, add_left_comm]

theorem PPoly.denoteG_eq_zero_of_coeff {α} [Ring α] (g : Nat → α) (hg : g 0 = 1) :
    ∀ (n : Nat) (p : PPoly), p.size ≤ n → (∀ c, p.coeff c = 0) → p.denoteG g = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hs h
    cases p with
    | num k => have := h 0; simp [coeff] at this; simp [denoteG, this, intCast_zero]
    | add => simp [size] at hs
  | succ n ih =>
    intro p hs h
    cases p with
    | num k => have := h 0; simp [coeff] at this; simp [denoteG, this, intCast_zero]
    | add k d v p =>
      rw [denoteG_removeCode g hg v, h v, intCast_zero, zero_mul, zero_add]
      apply ih
      · have := size_removeCode_le v p
        have : ((PPoly.add k d v p).removeCode v).size = (p.removeCode v).size := by simp [removeCode]
        simp [size] at hs; omega
      · intro c'; rw [coeff_removeCode]; split <;> simp [h]

theorem PPoly.denoteG_append {α} [Ring α] (g : Nat → α) (p q : PPoly) :
    (p.append q).denoteG g = p.denoteG g + q.denoteG g := by
  have hc : ∀ (q : PPoly) (k : Int), (append.addConst q k).denoteG g = q.denoteG g + k := by
    intro q k
    induction q with
    | num k' => simp [append.addConst, denoteG, intCast_add]
    | add k' d v q ih => simp [append.addConst, denoteG, ih, add_assoc]
  induction p with
  | num k => simp [append, denoteG, hc, add_comm]
  | add k d v p ih => simp [append, denoteG, ih, add_assoc]

theorem PPoly.denoteG_neg {α} [Ring α] (g : Nat → α) (p : PPoly) : p.neg.denoteG g = - p.denoteG g := by
  induction p with
  | num k => simp [neg, denoteG, intCast_neg]
  | add k d v p ih => simp [neg, denoteG, ih, intCast_neg, neg_mul, neg_add]

/-- `p` with its coefficients multiplied by `k`, without dropping zeros. -/
def PPoly.scale (k : Int) : PPoly → PPoly
  | .num k' => .num (k * k')
  | .add k' d v p => .add (k * k') d v (scale k p)

theorem PPoly.denoteG_scale {α} [Ring α] (g : Nat → α) (k : Int) (p : PPoly) :
    (p.scale k).denoteG g = k * p.denoteG g := by
  induction p with
  | num k' => simp [scale, denoteG, intCast_mul]
  | add k' d v p ih => simp [scale, denoteG, ih, intCast_mul, left_distrib, mul_assoc]

theorem PPoly.kron_scale (X k : Int) (p : PPoly) : (p.scale k).kron X = k * p.kron X := by
  induction p with
  | num k' => simp [scale, kron]
  | add k' d v p ih => simp [scale, kron, ih, Int.mul_add, Int.mul_assoc]

theorem PPoly.norm1_scale (k : Int) (p : PPoly) : (p.scale k).norm1 = k.natAbs * p.norm1 := by
  induction p with
  | num k' => simp [scale, norm1, Int.natAbs_mul]
  | add k' d v p ih => simp [scale, norm1, ih, Int.natAbs_mul, Nat.mul_add]

/-- The value of a constant expression (variables at `0`). -/
def Expr.evalConst : Expr → Int
  | .num k | .intCast k => k
  | .natCast n => n
  | .var _ => 0
  | .neg a => - evalConst a
  | .add a b => evalConst a + evalConst b
  | .sub a b => evalConst a - evalConst b
  | .mul a b => evalConst a * evalConst b
  | .pow a k => evalConst a ^ k

theorem Expr.denoteF_eq_evalConst {α} [CommRing α] (f : Nat → α) (e : Expr) (h : e.degB_k = 0) :
    e.denoteF f = (e.evalConst : α) := by
  induction e with
  | num k => show denoteInt k = _; rw [denoteInt_eq]; rfl
  | natCast n => show NatCast.natCast n = ((n : Int) : α); rw [intCast_natCast]
  | intCast k => rfl
  | var x => exact absurd (show (1 : Nat) = 0 from h) (by decide)
  | neg a ih => show - a.denoteF f = ((- a.evalConst : Int) : α); rw [ih h, intCast_neg]
  | add a b iha ihb =>
    have := Expr.le_max_k a.degB_k b.degB_k
    have h' : Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) = 0 := h
    show a.denoteF f + b.denoteF f = ((a.evalConst + b.evalConst : Int) : α)
    rw [iha (by omega), ihb (by omega), intCast_add]
  | sub a b iha ihb =>
    have := Expr.le_max_k a.degB_k b.degB_k
    have h' : Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) = 0 := h
    show a.denoteF f - b.denoteF f = ((a.evalConst - b.evalConst : Int) : α)
    rw [iha (by omega), ihb (by omega), intCast_sub]
  | mul a b iha ihb =>
    have h' : Nat.add a.degB_k b.degB_k = 0 := h
    show a.denoteF f * b.denoteF f = ((a.evalConst * b.evalConst : Int) : α)
    rw [iha (by simp at h'; omega), ihb (by simp at h'; omega), intCast_mul]
  | pow a k ih =>
    have h' : Nat.mul a.degB_k k = 0 := h
    show a.denoteF f ^ k = ((a.evalConst ^ k : Int) : α)
    rw [intCast_pow]
    rcases Nat.mul_eq_zero.mp h' with h'' | h''
    · rw [ih h'']
    · subst h''; rw [pow_zero, pow_zero]

theorem Expr.natAbs_evalConst_le (e : Expr) : e.evalConst.natAbs ≤ e.majorant_k := by
  induction e with
  | num k => show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | natCast n => show (n : Int).natAbs ≤ n; simp
  | intCast k => show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | var x => show (0 : Int).natAbs ≤ 1; simp
  | neg a ih => show (- a.evalConst).natAbs ≤ a.majorant_k; rw [Int.natAbs_neg]; exact ih
  | add a b iha ihb =>
    show (a.evalConst + b.evalConst).natAbs ≤ Nat.add a.majorant_k b.majorant_k
    have := Int.natAbs_add_le a.evalConst b.evalConst; simp only [Nat.add_eq]; omega
  | sub a b iha ihb =>
    show (a.evalConst - b.evalConst).natAbs ≤ Nat.add a.majorant_k b.majorant_k
    have := Int.natAbs_sub_le a.evalConst b.evalConst; simp only [Nat.add_eq]; omega
  | mul a b iha ihb =>
    show (a.evalConst * b.evalConst).natAbs ≤ Nat.mul a.majorant_k b.majorant_k
    rw [Int.natAbs_mul]; exact Nat.mul_le_mul iha ihb
  | pow a k ih =>
    show (a.evalConst ^ k).natAbs ≤ Nat.pow a.majorant_k k
    rw [Int.natAbs_pow]; exact Nat.pow_le_pow_left ih k

/-- The terms of a linear expression, with code `i + 1` for the variable `i` (only used in proofs). -/
noncomputable def Expr.toLin : Expr → PPoly
  | .num k | .intCast k => .num k
  | .natCast n => .num n
  | .var x => .add 1 1 (x + 1) (.num 0)
  | .neg a => (toLin a).neg
  | .add a b => (toLin a).append (toLin b)
  | .sub a b => (toLin a).append (toLin b).neg
  | .mul a b => if a.degB_k = 0 then (toLin b).scale a.evalConst else (toLin a).scale b.evalConst
  | .pow a k => if k = 0 then .num 1 else if k = 1 then toLin a else .num (a.evalConst ^ k)

/-- The value of `e` at the point `xᵢ = (2 ^ K) ^ (i + 1)`. -/
noncomputable def Expr.kronLinEval_k (K : Nat) (e : Expr) : Int :=
  Expr.rec (fun k => k) (fun n => Int.ofNat n) (fun k => k)
    (fun i => Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.add i 1))))
    (fun _ ih => Int.neg_k ih) (fun _ _ ih₁ ih₂ => Int.add_k ih₁ ih₂) (fun _ _ ih₁ ih₂ => Int.sub_k ih₁ ih₂)
    (fun _ _ ih₁ ih₂ => Int.mul_k ih₁ ih₂) (fun _ k ih => Int.pow_k ih k) e

theorem Expr.kronLinEval_k_eq (K : Nat) (e : Expr) :
    e.kronLinEval_k K = e.denoteF (fun i => ((2 : Int) ^ K) ^ (i + 1)) := by
  induction e with
  | num k => show k = denoteInt k; rw [denoteInt_eq]; rfl
  | natCast n => rfl
  | intCast k => rfl
  | var i =>
    show Int.ofNat (2 ^ (K * (i + 1))) = ((2 : Int) ^ K) ^ (i + 1)
    rw [← Int.pow_mul]; exact Int.natCast_pow 2 (K * (i + 1))
  | neg a ih =>
    show Int.neg_k (a.kronLinEval_k K) = - a.denoteF _; rw [Int.neg_k_eq, ih]; rfl
  | add a b iha ihb =>
    show Int.add_k (a.kronLinEval_k K) (b.kronLinEval_k K) = a.denoteF _ + b.denoteF _; rw [Int.add_k_eq, iha, ihb]; rfl
  | sub a b iha ihb =>
    show Int.sub_k (a.kronLinEval_k K) (b.kronLinEval_k K) = a.denoteF _ - b.denoteF _; rw [Int.sub_k_eq, iha, ihb]
  | mul a b iha ihb =>
    show Int.mul_k (a.kronLinEval_k K) (b.kronLinEval_k K) = a.denoteF _ * b.denoteF _; rw [Int.mul_k_eq, iha, ihb]; rfl
  | pow a k ih => show Int.pow_k (a.kronLinEval_k K) k = a.denoteF _ ^ k; rw [Int.pow_k_eq, ih]

/-- The valuation of the codes of `Expr.toLin`: the code `i + 1` is the variable `i`. -/
def PPoly.linVal {α} [Ring α] (f : Nat → α) (v : Nat) : α :=
  if v = 0 then 1 else f (v - 1)

theorem Expr.toLin_spec {α} [CommRing α] (f : Nat → α) (X : Int) (e : Expr) (h : e.degB_k ≤ 1) :
    (e.toLin).denoteG (PPoly.linVal f) = e.denoteF f ∧
    (e.toLin).kron X = e.denoteF (fun i => X ^ (i + 1)) ∧ (e.toLin).norm1 ≤ e.majorant_k := by
  induction e with
  | num k =>
    refine ⟨?_, ?_, ?_⟩
    · show (k : α) = denoteInt k; rw [denoteInt_eq]
    · show k = denoteInt k; rw [denoteInt_eq]; rfl
    · show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | natCast n =>
    refine ⟨?_, rfl, ?_⟩
    · show ((n : Int) : α) = NatCast.natCast n; rw [intCast_natCast]
    · show (n : Int).natAbs ≤ n; simp
  | intCast k =>
    refine ⟨rfl, rfl, ?_⟩
    show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | var x =>
    refine ⟨?_, ?_, ?_⟩
    · show ((1 : Int) : α) * PPoly.linVal f (x + 1) + ((0 : Int) : α) = f x
      simp [PPoly.linVal, intCast_one, one_mul, intCast_zero, add_zero]
    · show (1 : Int) * X ^ (x + 1) + 0 = X ^ (x + 1); omega
    · show (1 : Int).natAbs + (0 : Int).natAbs ≤ 1; simp
  | neg a ih =>
    have ih := ih h
    refine ⟨?_, ?_, ?_⟩
    · show a.toLin.neg.denoteG _ = - a.denoteF f; rw [PPoly.denoteG_neg, ih.1]
    · show a.toLin.neg.kron X = - a.denoteF _; rw [PPoly.kron_neg, ih.2.1]
    · show a.toLin.neg.norm1 ≤ a.majorant_k; rw [PPoly.norm1_neg]; exact ih.2.2
  | add a b iha ihb =>
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have h' : Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) ≤ 1 := h
    have iha := iha (by omega)
    have ihb := ihb (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (a.toLin.append b.toLin).denoteG _ = a.denoteF f + b.denoteF f; rw [PPoly.denoteG_append, iha.1, ihb.1]
    · show (a.toLin.append b.toLin).kron X = a.denoteF _ + b.denoteF _; rw [PPoly.kron_append, iha.2.1, ihb.2.1]
    · show (a.toLin.append b.toLin).norm1 ≤ Nat.add a.majorant_k b.majorant_k
      have := PPoly.norm1_append a.toLin b.toLin; simp only [Nat.add_eq]; omega
  | sub a b iha ihb =>
    have hm := Expr.le_max_k a.degB_k b.degB_k
    have h' : Bool.rec a.degB_k b.degB_k (Nat.blt a.degB_k b.degB_k) ≤ 1 := h
    have iha := iha (by omega)
    have ihb := ihb (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (a.toLin.append b.toLin.neg).denoteG _ = a.denoteF f - b.denoteF f
      rw [PPoly.denoteG_append, PPoly.denoteG_neg, iha.1, ihb.1, sub_eq_add_neg]
    · show (a.toLin.append b.toLin.neg).kron X = a.denoteF _ - b.denoteF _
      rw [PPoly.kron_append, PPoly.kron_neg, iha.2.1, ihb.2.1]; rfl
    · show (a.toLin.append b.toLin.neg).norm1 ≤ Nat.add a.majorant_k b.majorant_k
      have := PPoly.norm1_append a.toLin b.toLin.neg; rw [PPoly.norm1_neg] at this; simp only [Nat.add_eq]; omega
  | mul a b iha ihb =>
    have h' : Nat.add a.degB_k b.degB_k ≤ 1 := h
    by_cases ha : a.degB_k = 0
    · have ihb := ihb (by simp at h'; omega)
      have ca := Expr.denoteF_eq_evalConst f a ha
      have ca' := Expr.denoteF_eq_evalConst (fun i => X ^ (i + 1)) a ha
      have na := Expr.natAbs_evalConst_le a
      refine ⟨?_, ?_, ?_⟩
      · show (if a.degB_k = 0 then _ else _ : PPoly).denoteG _ = a.denoteF f * b.denoteF f
        rw [ite_eq_left ha, PPoly.denoteG_scale, ihb.1, ca]
      · show (if a.degB_k = 0 then _ else _ : PPoly).kron X = a.denoteF _ * b.denoteF _
        rw [ite_eq_left ha, PPoly.kron_scale, ihb.2.1, ca']; rfl
      · show (if a.degB_k = 0 then _ else _ : PPoly).norm1 ≤ Nat.mul a.majorant_k b.majorant_k
        rw [ite_eq_left ha, PPoly.norm1_scale, Nat.mul_eq]; exact Nat.mul_le_mul na ihb.2.2
    · have hb : b.degB_k = 0 := by simp at h'; omega
      have iha := iha (by simp at h'; omega)
      have cb := Expr.denoteF_eq_evalConst f b hb
      have cb' := Expr.denoteF_eq_evalConst (fun i => X ^ (i + 1)) b hb
      have nb := Expr.natAbs_evalConst_le b
      refine ⟨?_, ?_, ?_⟩
      · show (if a.degB_k = 0 then _ else _ : PPoly).denoteG _ = a.denoteF f * b.denoteF f
        rw [ite_eq_right ha, PPoly.denoteG_scale, iha.1, cb, CommSemiring.mul_comm]
      · show (if a.degB_k = 0 then _ else _ : PPoly).kron X = a.denoteF _ * b.denoteF _
        rw [ite_eq_right ha, PPoly.kron_scale, iha.2.1, cb', Int.mul_comm]; rfl
      · show (if a.degB_k = 0 then _ else _ : PPoly).norm1 ≤ Nat.mul a.majorant_k b.majorant_k
        rw [ite_eq_right ha, PPoly.norm1_scale, Nat.mul_eq, Nat.mul_comm]; exact Nat.mul_le_mul iha.2.2 nb
  | pow a k ih =>
    have h' : Nat.mul a.degB_k k ≤ 1 := h
    by_cases hk0 : k = 0
    · subst hk0
      refine ⟨?_, ?_, ?_⟩
      · show (if 0 = 0 then _ else _ : PPoly).denoteG _ = a.denoteF f ^ 0
        rw [ite_eq_left rfl, pow_zero]; exact intCast_one
      · show (if 0 = 0 then _ else _ : PPoly).kron X = a.denoteF _ ^ 0
        rw [ite_eq_left rfl, pow_zero]; rfl
      · show (if 0 = 0 then _ else _ : PPoly).norm1 ≤ Nat.pow a.majorant_k 0; rw [ite_eq_left rfl]; simp [PPoly.norm1]
    by_cases hk1 : k = 1
    · subst hk1
      have ih := ih (by simp at h'; omega)
      refine ⟨?_, ?_, ?_⟩
      · show (if 1 = 0 then _ else if 1 = 1 then _ else _ : PPoly).denoteG _ = a.denoteF f ^ 1
        rw [ite_eq_right (by decide), ite_eq_left rfl, pow_one, ih.1]
      · show (if 1 = 0 then _ else if 1 = 1 then _ else _ : PPoly).kron X = a.denoteF _ ^ 1
        rw [ite_eq_right (by decide), ite_eq_left rfl, ih.2.1]; exact (pow_one _).symm
      · show (if 1 = 0 then _ else if 1 = 1 then _ else _ : PPoly).norm1 ≤ Nat.pow a.majorant_k 1
        rw [ite_eq_right (by decide), ite_eq_left rfl, Nat.pow_eq, Nat.pow_one]; exact ih.2.2
    · have ha : a.degB_k = 0 := by
        rcases Nat.eq_zero_or_pos a.degB_k with h0 | h0
        · exact h0
        · have : 2 ≤ k := by omega
          have : 2 ≤ a.degB_k * k := Nat.le_trans (by omega) (Nat.mul_le_mul h0 this)
          have h'' : a.degB_k * k ≤ 1 := h'
          omega
      have ca := Expr.denoteF_eq_evalConst f a ha
      have ca' := Expr.denoteF_eq_evalConst (fun i => X ^ (i + 1)) a ha
      refine ⟨?_, ?_, ?_⟩
      · show (if k = 0 then _ else if k = 1 then _ else _ : PPoly).denoteG _ = a.denoteF f ^ k
        rw [ite_eq_right hk0, ite_eq_right hk1, ca, ← intCast_pow]; rfl
      · show (if k = 0 then _ else if k = 1 then _ else _ : PPoly).kron X = a.denoteF _ ^ k
        rw [ite_eq_right hk0, ite_eq_right hk1, ca']; rfl
      · show (if k = 0 then _ else if k = 1 then _ else _ : PPoly).norm1 ≤ Nat.pow a.majorant_k k
        rw [ite_eq_right hk0, ite_eq_right hk1]
        show (a.evalConst ^ k).natAbs ≤ _
        rw [Int.natAbs_pow, Nat.pow_eq]; exact Nat.pow_le_pow_left (Expr.natAbs_evalConst_le a) k

/--
An upper bound on `Expr.degB_k e`, with `Nat.lor` in place of the maximum: it is the degree when
the degree is at most `1`, and is cheaper to reduce.
-/
noncomputable def Expr.lin_k (e : Expr) : Nat :=
  Expr.rec (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 1) (fun _ ih => ih) (fun _ _ ih₁ ih₂ => Nat.lor ih₁ ih₂)
    (fun _ _ ih₁ ih₂ => Nat.lor ih₁ ih₂) (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂) (fun _ k ih => Nat.mul ih k) e

theorem Expr.max_le_lor (a b c d : Nat) (h₁ : a ≤ c) (h₂ : b ≤ d) : (Bool.rec a b (Nat.blt a b) : Nat) ≤ Nat.lor c d := by
  have := @Nat.left_le_or c d; have := @Nat.right_le_or c d
  rw [Expr.max_k_eq]; show max a b ≤ c ||| d; omega

theorem Expr.degB_le_lin_k (e : Expr) : e.degB_k ≤ e.lin_k := by
  induction e with
  | num | natCast | intCast | var => exact Nat.le_refl _
  | neg a ih => exact ih
  | add a b iha ihb | sub a b iha ihb => exact Expr.max_le_lor _ _ _ _ iha ihb
  | mul a b iha ihb => exact Nat.add_le_add iha ihb
  | pow a k ih => exact Nat.mul_le_mul_right k ih

/-- Checks that `a` and `b` are linear (`Expr.degB_k ≤ 1`, through `Expr.lin_k`). -/
noncomputable def Expr.linOk_k (a b : Expr) : Bool :=
  Bool.rec false (Nat.ble b.lin_k 1) (Nat.ble a.lin_k 1)

theorem Expr.eq_of_kronLin {α} [CommRing α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : linOk_k a b = true) (hK : kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    a.denote ctx = b.denote ctx := by
  have hl := PPoly.and_of_rec hl
  have ha := Nat.le_trans (Expr.degB_le_lin_k a) (Nat.le_of_ble_eq_true hl.1)
  have hb := Nat.le_trans (Expr.degB_le_lin_k b) (Nat.le_of_ble_eq_true hl.2)
  have hK : 2 * (a.majorant_k + b.majorant_k) < 2 ^ K := Nat.blt_eq.mp hK
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have sa := Expr.toLin_spec (Var.denote ctx) ((2 : Int) ^ K) a ha
  have sb := Expr.toLin_spec (Var.denote ctx) ((2 : Int) ^ K) b hb
  have hk : (a.toLin.append b.toLin.neg).kron ((2 : Int) ^ K) = 0 := by
    rw [PPoly.kron_append, PPoly.kron_neg, sa.2.1, sb.2.1, ← kronLinEval_k_eq, ← kronLinEval_k_eq, h]; omega
  have hn : 2 * ((a.toLin.append b.toLin.neg).norm1 : Int) < 2 ^ K := by
    have := PPoly.norm1_append a.toLin b.toLin.neg; rw [PPoly.norm1_neg] at this
    have : 2 * (a.toLin.append b.toLin.neg).norm1 < 2 ^ K := by have := sa.2.2; have := sb.2.2; omega
    have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
    rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this)
  have hz := PPoly.denoteG_eq_zero_of_coeff (PPoly.linVal (Var.denote ctx)) (by simp [PPoly.linVal]) _ _ (Nat.le_refl _)
    (fun c => PPoly.coeff_eq_zero_of_kron _ hX c _ hk hn)
  rw [PPoly.denoteG_append, PPoly.denoteG_neg, sa.1, sb.1] at hz
  rw [Expr.denote_eq_denoteF, Expr.denote_eq_denoteF, ← sub_eq_zero_iff, sub_eq_add_neg, hz]

theorem eq_true_of_kronLin {α} [CommRing α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : Expr.linOk_k a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    (a.denote ctx = b.denote ctx) = True :=
  eq_true (Expr.eq_of_kronLin ctx K a b hl hK h)

theorem le_true_of_kronLin {α} [CommRing α] [LE α] [IsPreorder α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : Expr.linOk_k a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    (a.denote ctx ≤ b.denote ctx) = True := by
  rw [Expr.eq_of_kronLin ctx K a b hl hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kronLin {α} [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α) (K : Nat)
    (a b : Expr) (hl : Expr.linOk_k a b = true) (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    (a.denote ctx < b.denote ctx) = False := by
  rw [Expr.eq_of_kronLin ctx K a b hl hK h]; exact eq_false Std.lt_irrefl

/-- The difference of `a` and `b` is the constant `k`, for the theorems `eq_false_of_sub`, `le_true_of_sub`, .... -/
theorem Expr.sub_eq_of_kronLin {α} [CommRing α] (ctx : Context α) (K : Nat) (a b : Expr) (k : Int)
    (hl : linOk_k a (b.add (.num k)) = true) (hK : kronOk_k K a (b.add (.num k)) = true)
    (h : a.kronLinEval_k K = (b.add (.num k)).kronLinEval_k K) : a.denote ctx - b.denote ctx = (k : α) := by
  have := Expr.eq_of_kronLin ctx K a (b.add (.num k)) hl hK h
  rw [this]; show b.denote ctx + denoteInt k - _ = _
  rw [denoteInt_eq, sub_eq_add_neg, add_comm, ← add_assoc, AddCommGroup.neg_add_cancel, zero_add]

/-- The difference of `a` and `b` is the constant `k`, by Kronecker substitution. -/
theorem Expr.sub_eq_of_kron {α} [CommRing α] (ctx : Context α) (K B : Nat) (a b : Expr) (k : Int)
    (hB : degOk_k B a (b.add (.num k)) = true) (hK : kronOk_k K a (b.add (.num k)) = true)
    (h : a.kronEval_k K B = (b.add (.num k)).kronEval_k K B) : a.denote ctx - b.denote ctx = (k : α) := by
  have := Expr.eq_of_kron ctx K B a (b.add (.num k)) hB hK h
  rw [this]; show b.denote ctx + denoteInt k - _ = _
  rw [denoteInt_eq, sub_eq_add_neg, add_comm, ← add_assoc, AddCommGroup.neg_add_cancel, zero_add]

/--
`Expr.lin_k e`, or at least `2` if `e` is not a semiring term (`Expr.semi_k`): one traversal checks
that a semiring term is linear.
-/
noncomputable def Expr.linS_k (e : Expr) : Nat :=
  Expr.rec (fun k => Int.rec (fun _ => 0) (fun _ => 2) k) (fun _ => 0) (fun _ => 2) (fun _ => 1)
    (fun _ _ => 2) (fun _ _ ih₁ ih₂ => Nat.lor ih₁ ih₂) (fun _ _ _ _ => 2)
    (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂) (fun _ k ih => Bool.rec (Nat.mul ih k) 2 (Nat.ble 2 ih)) e

theorem Expr.of_linS_k (e : Expr) (h : e.linS_k ≤ 1) : e.semi_k = true ∧ e.lin_k ≤ e.linS_k := by
  induction e with
  | num k =>
    cases k with
    | ofNat => exact ⟨rfl, Nat.le_refl _⟩
    | negSucc => exact (Nat.not_succ_le_self 1 h).elim
  | natCast => exact ⟨rfl, Nat.le_refl _⟩
  | intCast => exact (Nat.not_succ_le_self 1 h).elim
  | var => exact ⟨rfl, Nat.le_refl _⟩
  | neg => exact (Nat.not_succ_le_self 1 h).elim
  | sub => exact (Nat.not_succ_le_self 1 h).elim
  | add a b iha ihb =>
    have h' : a.linS_k ||| b.linS_k ≤ 1 := h
    have := @Nat.left_le_or a.linS_k b.linS_k; have := @Nat.right_le_or a.linS_k b.linS_k
    obtain ⟨sa, da⟩ := iha (by omega)
    obtain ⟨sb, db⟩ := ihb (by omega)
    refine ⟨show Bool.rec false b.semi_k a.semi_k = true by rw [sa, sb], ?_⟩
    show a.lin_k ||| b.lin_k ≤ a.linS_k ||| b.linS_k
    have h₃ : a.linS_k ≤ 1 := by omega
    have h₄ : b.linS_k ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h₃ with h₃ | h₃ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h₄ with h₄ | h₄ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_trans da (by omega)) with h₁ | h₁ <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_trans db (by omega)) with h₂ | h₂ <;>
    simp only [h₁, h₂, h₃, h₄] at da db ⊢ <;> first | decide | omega
  | mul a b iha ihb =>
    have h' : Nat.add a.linS_k b.linS_k ≤ 1 := h
    obtain ⟨sa, da⟩ := iha (by simp at h'; omega)
    obtain ⟨sb, db⟩ := ihb (by simp at h'; omega)
    refine ⟨show Bool.rec false b.semi_k a.semi_k = true by rw [sa, sb], ?_⟩
    show Nat.add a.lin_k b.lin_k ≤ Nat.add a.linS_k b.linS_k
    simp only [Nat.add_eq]; omega
  | pow a k ih =>
    have h' : (Bool.rec (Nat.mul a.linS_k k) 2 (Nat.ble 2 a.linS_k) : Nat) ≤ 1 := h
    cases hb : Nat.ble 2 a.linS_k
    · rw [hb] at h'
      have ha : a.linS_k ≤ 1 := Nat.le_of_lt_succ (Nat.gt_of_not_le (fun hle => by rw [Nat.ble_eq.mpr hle] at hb; cases hb))
      obtain ⟨sa, da⟩ := ih ha
      refine ⟨sa, ?_⟩
      show Nat.mul a.lin_k k ≤ Bool.rec (Nat.mul a.linS_k k) 2 (Nat.ble 2 a.linS_k)
      rw [hb]; exact Nat.mul_le_mul_right k da
    · rw [hb] at h'; exact (Nat.not_succ_le_self 1 h').elim

/-- Checks that `a` and `b` are linear semiring terms (`Expr.linS_k`). -/
noncomputable def Expr.linSOk_k (a b : Expr) : Bool :=
  Bool.rec false (Nat.ble b.linS_k 1) (Nat.ble a.linS_k 1)

theorem Expr.of_linSOk_k {a b : Expr} (h : linSOk_k a b = true) :
    Bool.rec false b.semi_k a.semi_k = true ∧ linOk_k a b = true := by
  have h := PPoly.and_of_rec h
  obtain ⟨sa, da⟩ := of_linS_k a (Nat.le_of_ble_eq_true h.1)
  obtain ⟨sb, db⟩ := of_linS_k b (Nat.le_of_ble_eq_true h.2)
  refine ⟨by rw [sa, sb], ?_⟩
  unfold linOk_k
  rw [Nat.ble_eq.mpr (Nat.le_trans da (Nat.le_of_ble_eq_true h.1)), Nat.ble_eq.mpr (Nat.le_trans db (Nat.le_of_ble_eq_true h.2))]

theorem Expr.eq_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : linSOk_k a b = true) (hK : kronOk_k K a b = true)
    (h : a.kronLinEval_k K = b.kronLinEval_k K) : a.denoteS ctx = b.denoteS ctx := by
  obtain ⟨hS, hl⟩ := of_linSOk_k hl
  have hS := semi_k_and hS
  apply Ring.OfSemiring.toQ_inj
  rw [← Expr.denoteAsRing_eq, ← Expr.denoteAsRing_eq, ← denote_mapCtx_toQ ctx a hS.1, ← denote_mapCtx_toQ ctx b hS.2]
  exact Expr.eq_of_kronLin _ K a b hl hK h

theorem eq_true_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : Expr.linSOk_k a b = true) (hK : Expr.kronOk_k K a b = true)
    (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx = b.denoteS ctx) = True :=
  eq_true (Expr.eq_of_kronLinS ctx K a b hl hK h)

theorem le_true_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [IsPreorder α] (ctx : Context α) (K : Nat)
    (a b : Expr) (hl : Expr.linSOk_k a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx ≤ b.denoteS ctx) = True := by
  rw [Expr.eq_of_kronLinS ctx K a b hl hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    (ctx : Context α) (K : Nat) (a b : Expr) (hl : Expr.linSOk_k a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx < b.denoteS ctx) = False := by
  rw [Expr.eq_of_kronLinS ctx K a b hl hK h]; exact eq_false Std.lt_irrefl

/-!
Kronecker certificates for `grind`'s Gröbner steps: a chain `p = p₁ + Σ kᵢ * mᵢ * qᵢ` of stated
polynomials is checked by comparing values at the point (`Stepwise.simpsK`, `Stepwise.d_stepsK`).
In characteristic `c`, the difference is `c * E` for a stated polynomial `E` (`Stepwise.simpsKC`).
-/

/-- `a * 2 ^ s` for kernel reduction. -/
noncomputable def Int.shl_k (a : Int) (s : Nat) : Int :=
  Int.rec (fun n => Int.ofNat (Nat.shiftLeft n s)) (fun n => Int.negOfNat_k (Nat.shiftLeft (Nat.add n 1) s)) a

theorem Int.shl_k_eq (a : Int) (s : Nat) : Int.shl_k a s = a * 2 ^ s := by
  have h2 : ((2 ^ s : Nat) : Int) = (2 : Int) ^ s := Int.natCast_pow 2 s
  cases a with
  | ofNat n =>
    show Int.ofNat (n <<< s) = _
    rw [Nat.shiftLeft_eq, ← h2]; rfl
  | negSucc n =>
    show Int.negOfNat_k ((n + 1) <<< s) = _
    rw [Int.negOfNat_k_eq, Nat.shiftLeft_eq, Int.negSucc_eq, ← h2, Int.negOfNat_eq, Int.neg_mul]
    rfl

/-- Adds the integers of `ps` by levels of pairwise additions, so that the kernel evaluates sums of nesting depth logarithmic in their number. -/
noncomputable def Int.pairs_k (ps : List Int) : Option Int → List Int :=
  List.rec (motive := fun _ => Option Int → List Int)
    (fun pend => Option.rec [] (fun p => [p]) pend)
    (fun a _ ih pend => Option.rec (ih (some a)) (fun p => Int.add_k p a :: ih none) pend)
    ps

noncomputable def Int.sumGo_k (fuel : List Int) : List Int → Int :=
  List.rec (motive := fun _ => List Int → Int)
    (fun ps => List.rec (Int.ofNat 0) (fun a _ ih => Int.add_k a ih) ps)
    (fun _ _ ih ps => List.rec (Int.ofNat 0) (fun a rest _ => List.rec a (fun _ _ _ => ih (Int.pairs_k ps none)) rest) ps)
    fuel

noncomputable def Int.sumB_k (ps : List Int) : Int :=
  Int.sumGo_k ps ps

theorem Int.pairs_k_sum (ps : List Int) (pend : Option Int) :
    (Int.pairs_k ps pend).foldr (· + ·) 0 = pend.elim 0 id + ps.foldr (· + ·) 0 := by
  induction ps generalizing pend with
  | nil => cases pend <;> simp [Int.pairs_k, Option.elim]
  | cons a ps ih =>
    cases pend with
    | none => show (Int.pairs_k ps (some a)).foldr (· + ·) 0 = _; rw [ih]; simp [Option.elim]
    | some p => show Int.add_k p a + (Int.pairs_k ps none).foldr (· + ·) 0 = _; rw [ih, Int.add_k_eq]; simp [Option.elim]; omega

theorem Int.sumGo_k_eq (fuel ps : List Int) : Int.sumGo_k fuel ps = ps.foldr (· + ·) 0 := by
  induction fuel generalizing ps with
  | nil =>
    show List.rec (motive := fun _ => Int) (Int.ofNat 0) (fun a _ ih => Int.add_k a ih) ps = _
    induction ps with
    | nil => rfl
    | cons a ps ih => show Int.add_k a _ = _; rw [ih, Int.add_k_eq]; rfl
  | cons _ fuel ih =>
    cases ps with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => show a = a + 0; omega
      | cons b rest =>
        show Int.sumGo_k fuel (Int.pairs_k (a :: b :: rest) none) = _
        rw [ih, Int.pairs_k_sum]; simp [Option.elim]

theorem Int.sumB_k_eq (ps : List Int) : Int.sumB_k ps = ps.foldr (· + ·) 0 := Int.sumGo_k_eq ps ps

/-- The values of the terms of `p` at the point `xᵢ = (2 ^ K) ^ (B ^ i)`. -/
noncomputable def Poly.kronTerms_k (K B : Nat) (p : Poly) : List Int :=
  Poly.rec (fun k => [k]) (fun k m _ ih => Int.shl_k k (Nat.mul K (Mon.code_k B m)) :: ih) p

/-- The value of `p` at the point `xᵢ = (2 ^ K) ^ (B ^ i)`. -/
noncomputable def Poly.kron_k (K B : Nat) (p : Poly) : Int :=
  Int.sumB_k (p.kronTerms_k K B)

noncomputable def Poly.norm1_k (p : Poly) : Nat :=
  Poly.rec (fun k => Int.natAbs_k k) (fun k _ _ ih => Nat.add (Int.natAbs_k k) ih) p

theorem Poly.kron_k_eq (K B : Nat) (p : Poly) : p.kron_k K B = (p.toPP_k B).kron (2 ^ K) := by
  rw [Poly.kron_k, Int.sumB_k_eq]
  induction p with
  | num k => show k + 0 = k; omega
  | add k m p ih =>
    show Int.shl_k k (Nat.mul K (Mon.code_k B m)) + (p.kronTerms_k K B).foldr (· + ·) 0 = k * (2 ^ K) ^ (Mon.code_k B m) + _
    rw [Int.shl_k_eq, ih, ← Int.pow_mul]; rfl

theorem Poly.norm1_k_eq (B : Nat) (p : Poly) : p.norm1_k = (p.toPP_k B).norm1 := by
  induction p with
  | num k => show Int.natAbs_k k = _; rw [Int.natAbs_k_eq]; rfl
  | add k m p ih => show Nat.add (Int.natAbs_k k) p.norm1_k = _; rw [Int.natAbs_k_eq, ih]; rfl

noncomputable def PPoly.kronTerms_k (K : Nat) (p : PPoly) : List Int :=
  PPoly.rec (fun k => [k]) (fun k _ v _ ih => Int.shl_k k (Nat.mul K v) :: ih) p

/-- The value `PPoly.kron (2 ^ K)` of a packed polynomial, for kernel reduction. -/
noncomputable def PPoly.kron_k (K : Nat) (p : PPoly) : Int :=
  Int.sumB_k (p.kronTerms_k K)

noncomputable def PPoly.norm1_k (p : PPoly) : Nat :=
  PPoly.rec (fun k => Int.natAbs_k k) (fun k _ _ _ ih => Nat.add (Int.natAbs_k k) ih) p

theorem PPoly.kron_k_eq (K : Nat) (p : PPoly) : p.kron_k K = p.kron (2 ^ K) := by
  rw [PPoly.kron_k, Int.sumB_k_eq]
  induction p with
  | num k => show k + 0 = k; omega
  | add k d v p ih =>
    show Int.shl_k k (Nat.mul K v) + (p.kronTerms_k K).foldr (· + ·) 0 = k * (2 ^ K) ^ v + _
    rw [Int.shl_k_eq, ih, ← Int.pow_mul]; rfl

theorem PPoly.norm1_k_eq (p : PPoly) : p.norm1_k = p.norm1 := by
  induction p with
  | num k => show Int.natAbs_k k = _; rw [Int.natAbs_k_eq]; rfl
  | add k d v p ih => show Nat.add (Int.natAbs_k k) p.norm1_k = _; rw [Int.natAbs_k_eq, ih]; rfl

/-- The multiples `k * m * q` of a Gröbner step. -/
inductive KList where
  | nil
  | cons (k : Int) (m : Mon) (q : Poly) (ls : KList)

/-- The values of the multiples of `ls` at the point. -/
noncomputable def KList.kronTerms_k (K B : Nat) (ls : KList) : List Int :=
  KList.rec [] (fun k m q _ ih => Int.mul_k k (Int.shl_k (q.kron_k K B) (Nat.mul K (Mon.code_k B m))) :: ih) ls

noncomputable def KList.kron_k (K B : Nat) (ls : KList) : Int :=
  Int.sumB_k (ls.kronTerms_k K B)

noncomputable def KList.norm_k (ls : KList) : Nat :=
  KList.rec 0 (fun k _ q _ ih => Nat.add (Nat.mul (Int.natAbs_k k) q.norm1_k) ih) ls

noncomputable def KList.ok_k (B : Nat) (ls : KList) : Bool :=
  KList.rec true (fun _ m q _ ih => Bool.rec false ih (Nat.blt (Nat.add (Mon.degree_k m) q.maxDeg_k) B)) ls

/-- Every polynomial of `ls` denotes `0`. -/
noncomputable def KList.AllZero {α} [Ring α] (ctx : Context α) (ls : KList) : Prop :=
  KList.rec True (fun _ _ q _ ih => q.denote ctx = 0 ∧ ih) ls

theorem KList.allZero_nil {α} [Ring α] (ctx : Context α) : KList.nil.AllZero ctx := trivial

theorem KList.allZero_cons {α} [Ring α] (ctx : Context α) (k : Int) (m : Mon) (q : Poly) (ls : KList)
    (hq : q.denote ctx = 0) (hls : ls.AllZero ctx) : (KList.cons k m q ls).AllZero ctx := ⟨hq, hls⟩

/-- The multiples of `ls` with packed monomials, appended. -/
noncomputable def KList.toPP (B : Nat) (ls : KList) : PPoly :=
  KList.rec (.num 0) (fun k m q _ ih => ((q.toPP_k B).mulMonN_k (fun k => k) k (Mon.degree_k m) (Mon.code_k B m)).append ih) ls

theorem PPoly.kron_mulMonN (X : Int) (k : Int) (d v : Nat) (p : PPoly) :
    (p.mulMonN_k (fun k => k) k d v).kron X = k * X ^ v * p.kron X := by
  induction p with
  | num k' =>
    unfold mulMonN_k; dsimp only
    cases hv : Nat.beq v 0
    · dsimp only
      cases hz : Int.beqZero_k (Int.mul_k k k')
      · show Int.mul_k k k' * X ^ v + 0 = _
        rw [Int.mul_k_eq]; show k * k' * X ^ v + 0 = _
        rw [Int.add_zero, Int.mul_assoc, Int.mul_comm k', ← Int.mul_assoc]; rfl
      · rw [Int.beqZero_k_eq, Int.mul_k_eq] at hz
        have : k * k' = 0 := by simpa using hz
        show (0 : Int) = _
        rw [Int.mul_assoc, Int.mul_comm (X ^ v), ← Int.mul_assoc]; show (0 : Int) = k * k' * X ^ v; rw [this, Int.zero_mul]
    · have : v = 0 := Nat.eq_of_beq_eq_true hv
      subst this
      show Int.mul_k k k' = _
      rw [Int.mul_k_eq, Int.pow_zero, Int.mul_one]; rfl
  | add k' d' v' p ih =>
    show (Bool.rec (.add (Int.mul_k k k') (Nat.add d d') (Nat.add v v') (p.mulMonN_k (fun k => k) k d v)) (p.mulMonN_k (fun k => k) k d v)
      (Int.beqZero_k (Int.mul_k k k')) : PPoly).kron X = _
    cases hz : Int.beqZero_k (Int.mul_k k k')
    · show Int.mul_k k k' * X ^ (Nat.add v v') + (p.mulMonN_k (fun k => k) k d v).kron X = k * X ^ v * (k' * X ^ v' + p.kron X)
      rw [ih, Int.mul_k_eq, Nat.add_eq, Int.pow_add, Int.mul_add]
      show k * k' * (X ^ v * X ^ v') + _ = _
      congr 1
      simp only [Int.mul_assoc, Int.mul_left_comm]
    · rw [Int.beqZero_k_eq, Int.mul_k_eq] at hz
      have : k * k' = 0 := by simpa using hz
      show (p.mulMonN_k (fun k => k) k d v).kron X = k * X ^ v * (k' * X ^ v' + p.kron X)
      rw [ih, Int.mul_add]
      have : k * X ^ v * (k' * X ^ v') = 0 := by
        rw [show k * X ^ v * (k' * X ^ v') = (k * k') * (X ^ v * X ^ v') by
          simp only [Int.mul_assoc, Int.mul_left_comm], this, Int.zero_mul]
      rw [this, Int.zero_add]

theorem PPoly.norm1_mulMonN (k : Int) (d v : Nat) (p : PPoly) :
    (p.mulMonN_k (fun k => k) k d v).norm1 ≤ k.natAbs * p.norm1 := by
  induction p with
  | num k' =>
    unfold mulMonN_k; dsimp only
    cases Nat.beq v 0
    · dsimp only
      cases Int.beqZero_k (Int.mul_k k k')
      · show (Int.mul_k k k').natAbs + (Int.ofNat 0).natAbs ≤ _
        rw [Int.mul_k_eq]; show (k * k').natAbs + 0 ≤ _; rw [Int.natAbs_mul]; simp [norm1]
      · show (Int.ofNat 0).natAbs ≤ _; simp
    · show (Int.mul_k k k').natAbs ≤ _; rw [Int.mul_k_eq]; show (k * k').natAbs ≤ _; rw [Int.natAbs_mul]; simp [norm1]
  | add k' d' v' p ih =>
    show (Bool.rec (.add (Int.mul_k k k') (Nat.add d d') (Nat.add v v') (p.mulMonN_k (fun k => k) k d v)) (p.mulMonN_k (fun k => k) k d v)
      (Int.beqZero_k (Int.mul_k k k')) : PPoly).norm1 ≤ _
    cases Int.beqZero_k (Int.mul_k k k')
    · show (Int.mul_k k k').natAbs + (p.mulMonN_k (fun k => k) k d v).norm1 ≤ _
      rw [Int.mul_k_eq]; show (k * k').natAbs + _ ≤ _
      rw [Int.natAbs_mul]; simp only [norm1, Nat.mul_add]; omega
    · show (p.mulMonN_k (fun k => k) k d v).norm1 ≤ _
      simp only [norm1, Nat.mul_add]; omega

theorem KList.toPP_spec {α} [CommRing α] (ctx : Context α) (K B : Nat) (hB : 1 < B) (ls : KList) (hok : ls.ok_k B = true) :
    (ls.toPP B).kron (2 ^ K) = ls.kron_k K B ∧ (ls.toPP B).norm1 ≤ ls.norm_k ∧
    (ls.AllZero ctx → (ls.toPP B).denote (Var.denote ctx) B = 0) := by
  induction ls with
  | nil => exact ⟨rfl, Nat.le_refl _, fun _ => intCast_zero⟩
  | cons k m q ls ih =>
    have hok : Bool.rec false (ls.ok_k B) (Nat.blt (Nat.add (Mon.degree_k m) q.maxDeg_k) B) = true := hok
    have hok := PPoly.and_of_rec hok
    have ih := ih hok.2
    have hd := Nat.blt_eq.mp hok.1
    rw [Mon.degree_k_eq_degree, Nat.add_eq] at hd
    refine ⟨?_, ?_, fun hz => ?_⟩
    · show (PPoly.append _ (ls.toPP B)).kron (2 ^ K) = Int.sumB_k (Int.mul_k k (Int.shl_k (q.kron_k K B) (Nat.mul K (Mon.code_k B m))) :: ls.kronTerms_k K B)
      rw [PPoly.kron_append, PPoly.kron_mulMonN, ih.1, KList.kron_k, Int.sumB_k_eq, Int.sumB_k_eq]
      show _ = Int.mul_k k (Int.shl_k (q.kron_k K B) (Nat.mul K (Mon.code_k B m))) + _
      rw [Int.mul_k_eq, Int.shl_k_eq, Poly.kron_k_eq]
      show k * ((2 : Int) ^ K) ^ (Mon.code_k B m) * _ + _ = k * (_ * (2 : Int) ^ (K * Mon.code_k B m)) + _
      rw [Int.pow_mul, Int.mul_assoc, Int.mul_comm (((2 : Int) ^ K) ^ (Mon.code_k B m))]
    · show (PPoly.append _ (ls.toPP B)).norm1 ≤ Nat.add (Nat.mul (Int.natAbs_k k) q.norm1_k) ls.norm_k
      have := PPoly.norm1_append ((q.toPP_k B).mulMonN_k (fun k => k) k (Mon.degree_k m) (Mon.code_k B m)) (ls.toPP B)
      have := PPoly.norm1_mulMonN k (Mon.degree_k m) (Mon.code_k B m) (q.toPP_k B)
      rw [Int.natAbs_k_eq, Poly.norm1_k_eq B, Nat.add_eq, Nat.mul_eq]
      have := ih.2.1
      omega
    · obtain ⟨hq, hz⟩ := hz
      show (PPoly.append _ (ls.toPP B)).denote (Var.denote ctx) B = 0
      have hp := Poly.toPP_k_spec ctx hB q (by omega)
      have hc := Mon.code_k_spec ctx hB m (by omega)
      have hm := PPoly.mulMonN_k_spec (Var.denote ctx) (fun k => k) (fun _ => rfl) B m.degree q.maxDeg_k hB k (Mon.degree_k m)
        (m.code_k B) (by rw [hc.1]; exact Nat.le_refl _) hd _ hp.2
      rw [PPoly.denote_append, hm.1, hp.1, hq, mul_zero, ih.2.2 hz, add_zero]

/--
Multiples `M * q` of polynomials `q` that denote `0`, with one cofactor `M = Σ kᵢ * mᵢ` per `q`:
the multiples `kᵢ * mᵢ * q` of a chain usually share few polynomials `q`.
-/
inductive MList where
  | nil
  | cons (M q : Poly) (ls : MList)

/-- The values of the multiples of `ls` at the point. -/
noncomputable def MList.kronTerms_k (K B : Nat) (ls : MList) : List Int :=
  MList.rec [] (fun M q _ ih => Int.mul_k (M.kron_k K B) (q.kron_k K B) :: ih) ls

noncomputable def MList.kron_k (K B : Nat) (ls : MList) : Int :=
  Int.sumB_k (ls.kronTerms_k K B)

noncomputable def MList.norm_k (ls : MList) : Nat :=
  MList.rec 0 (fun M q _ ih => Nat.add (Nat.mul M.norm1_k q.norm1_k) ih) ls

noncomputable def MList.ok_k (B : Nat) (ls : MList) : Bool :=
  MList.rec true (fun M q _ ih => Bool.rec false ih (Nat.blt (Nat.add M.maxDeg_k q.maxDeg_k) B)) ls

/-- Every polynomial `q` of `ls` denotes `0`. -/
noncomputable def MList.AllZero {α} [Ring α] (ctx : Context α) (ls : MList) : Prop :=
  MList.rec True (fun _ q _ ih => q.denote ctx = 0 ∧ ih) ls

theorem MList.allZero_nil {α} [Ring α] (ctx : Context α) : MList.nil.AllZero ctx := trivial

theorem MList.allZero_cons {α} [Ring α] (ctx : Context α) (M q : Poly) (ls : MList)
    (hq : q.denote ctx = 0) (hls : ls.AllZero ctx) : (MList.cons M q ls).AllZero ctx := ⟨hq, hls⟩

/-- The terms of the multiples of `ls`, packed in base `B`. -/
noncomputable def MList.toPP (B : Nat) (ls : MList) : PPoly :=
  MList.rec (.num 0) (fun M q _ ih => ((M.toPP_k B).mulB_k (q.toPP_k B)).append ih) ls

theorem MList.toPP_spec {α} [CommRing α] (ctx : Context α) (K B : Nat) (hB : 1 < B) (ls : MList) (hok : ls.ok_k B = true) :
    (ls.toPP B).kron (2 ^ K) = ls.kron_k K B ∧ (ls.toPP B).norm1 ≤ ls.norm_k ∧
    (ls.AllZero ctx → (ls.toPP B).denote (Var.denote ctx) B = 0) := by
  induction ls with
  | nil => exact ⟨rfl, Nat.le_refl _, fun _ => intCast_zero⟩
  | cons M q ls ih =>
    have hok : Bool.rec false (ls.ok_k B) (Nat.blt (Nat.add M.maxDeg_k q.maxDeg_k) B) = true := hok
    have hok := PPoly.and_of_rec hok
    have ih := ih hok.2
    have hd := Nat.blt_eq.mp hok.1
    rw [Nat.add_eq] at hd
    have dM := (Poly.toPP_k_spec ctx hB M (by omega)).2
    have dq := (Poly.toPP_k_spec ctx hB q (by omega)).2
    refine ⟨?_, ?_, fun hz => ?_⟩
    · show (PPoly.append _ (ls.toPP B)).kron (2 ^ K) = Int.sumB_k (Int.mul_k (M.kron_k K B) (q.kron_k K B) :: ls.kronTerms_k K B)
      have hm := PPoly.mulB_k_spec (fun i => ((2 : Int) ^ K) ^ (B ^ i)) B M.maxDeg_k q.maxDeg_k hB hd _ _ dM dq
      rw [PPoly.kron_append, ← PPoly.denote_kron _ hB, hm.1, PPoly.denote_kron _ hB, PPoly.denote_kron _ hB, ih.1,
        MList.kron_k, Int.sumB_k_eq, Int.sumB_k_eq]
      show _ = Int.mul_k (M.kron_k K B) (q.kron_k K B) + _
      rw [Int.mul_k_eq, Poly.kron_k_eq, Poly.kron_k_eq]; rfl
    · show (PPoly.append _ (ls.toPP B)).norm1 ≤ Nat.add (Nat.mul M.norm1_k q.norm1_k) ls.norm_k
      have := PPoly.norm1_append ((M.toPP_k B).mulB_k (q.toPP_k B)) (ls.toPP B)
      have := PPoly.norm1_mulB_k (M.toPP_k B) (q.toPP_k B)
      rw [Poly.norm1_k_eq B M, Poly.norm1_k_eq B q, Nat.add_eq, Nat.mul_eq]
      have := ih.2.1
      omega
    · obtain ⟨hq, hz⟩ := hz
      show (PPoly.append _ (ls.toPP B)).denote (Var.denote ctx) B = 0
      have hm := PPoly.mulB_k_spec (Var.denote ctx) B M.maxDeg_k q.maxDeg_k hB hd _ _ dM dq
      have sq := Poly.toPP_k_spec ctx hB q (by omega)
      rw [PPoly.denote_append, hm.1, sq.1, hq, mul_zero, ih.2.2 hz, add_zero]

theorem PPoly.kron_mulConst_k (X : Int) (k : Int) (p : PPoly) : (p.mulConst_k k).kron X = k * p.kron X := by
  unfold mulConst_k
  cases hk : Int.beqZero_k k
  · dsimp only
    induction p with
    | num k' => show Int.mul_k k k' = _; rw [Int.mul_k_eq]; rfl
    | add k' d v p ih =>
      show Int.mul_k k k' * X ^ v + _ = k * (k' * X ^ v + p.kron X)
      rw [ih, Int.mul_k_eq, Int.mul_add]
      show k * k' * X ^ v + _ = _
      rw [Int.mul_assoc]
  · rw [Int.beqZero_k_eq] at hk
    have : k = 0 := by simpa using hk
    subst this; show (0 : Int) = 0 * _; rw [Int.zero_mul]

/-- `p` and `p₁ + Σ ls + c * E` have the same value at the point, so they denote the same. -/
theorem KList.denote_eq {α} [CommRing α] (ctx : Context α) (K B c : Nat) (p₁ p : Poly) (E : PPoly) (ls : KList)
    (hB : 1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ ls.ok_k B = true)
    (hK : 2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K)
    (h : p.kron_k K B = p₁.kron_k K B + ls.kron_k K B + c * E.kron_k K) (hz : ls.AllZero ctx) :
    p.denote ctx = p₁.denote ctx + (c : α) * E.denote (Var.denote ctx) B := by
  obtain ⟨hB, hp, hp₁, hok⟩ := hB
  have hl := KList.toPP_spec ctx K B hB ls hok
  have sp := Poly.toPP_k_spec ctx hB p hp
  have sp₁ := Poly.toPP_k_spec ctx hB p₁ hp₁
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have hEc := PPoly.mulConst_k_spec (Var.denote ctx) B (B - 1) (c : Int) E
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (p.toPP_k B)
    ((p₁.toPP_k B).append ((ls.toPP B).append (E.mulConst_k (c : Int))))
    (by
      rw [PPoly.kron_append, PPoly.kron_append, PPoly.kron_mulConst_k, ← Poly.kron_k_eq, ← Poly.kron_k_eq,
        ← PPoly.kron_k_eq K E, hl.1, h, Int.add_assoc])
    (by
      have h₁ := PPoly.norm1_append (p₁.toPP_k B) ((ls.toPP B).append (E.mulConst_k (c : Int)))
      have h₂ := PPoly.norm1_append (ls.toPP B) (E.mulConst_k (c : Int))
      have h₃ := PPoly.norm1_mulConst_k (c : Int) E
      rw [← Poly.norm1_k_eq] at h₁
      rw [← PPoly.norm1_k_eq E] at h₃
      have h₄ := hl.2.1
      rw [show ((c : Int)).natAbs = c from rfl] at h₃
      have : 2 * ((p.toPP_k B).norm1 + ((p₁.toPP_k B).append ((ls.toPP B).append (E.mulConst_k (c : Int)))).norm1) < 2 ^ K := by
        rw [← Poly.norm1_k_eq]
        have := Nat.mul_le_mul_left c (Nat.le_refl E.norm1_k)
        omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [PPoly.denote_append, PPoly.denote_append, hEc.1, sp.1, sp₁.1, hl.2.2 hz, zero_add] at heq
  rw [heq]; congr 1; rw [intCast_natCast]

theorem MList.denote_eq {α} [CommRing α] (ctx : Context α) (K B c : Nat) (p₁ p : Poly) (E : PPoly) (ls : MList)
    (hB : 1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ ls.ok_k B = true)
    (hK : 2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K)
    (h : p.kron_k K B = p₁.kron_k K B + ls.kron_k K B + c * E.kron_k K) (hz : ls.AllZero ctx) :
    p.denote ctx = p₁.denote ctx + (c : α) * E.denote (Var.denote ctx) B := by
  obtain ⟨hB, hp, hp₁, hok⟩ := hB
  have hl := MList.toPP_spec ctx K B hB ls hok
  have sp := Poly.toPP_k_spec ctx hB p hp
  have sp₁ := Poly.toPP_k_spec ctx hB p₁ hp₁
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have hEc := PPoly.mulConst_k_spec (Var.denote ctx) B (B - 1) (c : Int) E
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (p.toPP_k B)
    ((p₁.toPP_k B).append ((ls.toPP B).append (E.mulConst_k (c : Int))))
    (by
      rw [PPoly.kron_append, PPoly.kron_append, PPoly.kron_mulConst_k, ← Poly.kron_k_eq, ← Poly.kron_k_eq,
        ← PPoly.kron_k_eq K E, hl.1, h, Int.add_assoc])
    (by
      have h₁ := PPoly.norm1_append (p₁.toPP_k B) ((ls.toPP B).append (E.mulConst_k (c : Int)))
      have h₂ := PPoly.norm1_append (ls.toPP B) (E.mulConst_k (c : Int))
      have h₃ := PPoly.norm1_mulConst_k (c : Int) E
      rw [← Poly.norm1_k_eq] at h₁
      rw [← PPoly.norm1_k_eq E] at h₃
      have h₄ := hl.2.1
      rw [show ((c : Int)).natAbs = c from rfl] at h₃
      have : 2 * ((p.toPP_k B).norm1 + ((p₁.toPP_k B).append ((ls.toPP B).append (E.mulConst_k (c : Int)))).norm1) < 2 ^ K := by
        rw [← Poly.norm1_k_eq]
        have := Nat.mul_le_mul_left c (Nat.le_refl E.norm1_k)
        omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [PPoly.denote_append, PPoly.denote_append, hEc.1, sp.1, sp₁.1, hl.2.2 hz, zero_add] at heq
  rw [heq]; congr 1; rw [intCast_natCast]

/-- `e` and `p + c * E` have the same value at the point, so they denote the same. -/
theorem Expr.denote_eq_of_kron_poly {α} [CommRing α] (ctx : Context α) (K B c : Nat) (e : Expr) (p : Poly) (E : PPoly)
    (hB : 1 < B ∧ e.degB_k < B ∧ p.maxDeg_k < B)
    (hK : 2 * (e.majorant_k + p.norm1_k + c * E.norm1_k) < 2 ^ K)
    (h : e.kronEval_k K B = p.kron_k K B + c * E.kron_k K) :
    e.denote ctx = p.denote ctx + (c : α) * E.denote (Var.denote ctx) B := by
  obtain ⟨hB, he, hp⟩ := hB
  have sp := Poly.toPP_k_spec ctx hB p hp
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have hEc := PPoly.mulConst_k_spec (Var.denote ctx) B (B - 1) (c : Int) E
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (e.toPP_k B)
    ((p.toPP_k B).append (E.mulConst_k (c : Int)))
    (by
      rw [PPoly.kron_append, PPoly.kron_mulConst_k, ← Poly.kron_k_eq, ← PPoly.kron_k_eq K E, ← PPoly.denote_kron _ hB,
        denote_toPP_k _ B hB e he, ← kronEval_k_eq, h])
    (by
      have h₁ := PPoly.norm1_append (p.toPP_k B) (E.mulConst_k (c : Int))
      have h₃ := PPoly.norm1_mulConst_k (c : Int) E
      rw [← Poly.norm1_k_eq] at h₁
      rw [← PPoly.norm1_k_eq E] at h₃
      rw [show ((c : Int)).natAbs = c from rfl] at h₃
      have h₄ := norm1_toPPAcc_k B e (.num (Int.ofNat 0))
      rw [show (PPoly.num (Int.ofNat 0)).norm1 = 0 from rfl, Nat.add_zero] at h₄
      have : 2 * ((e.toPP_k B).norm1 + ((p.toPP_k B).append (E.mulConst_k (c : Int))).norm1) < 2 ^ K := by
        have := Nat.mul_le_mul_left c (Nat.le_refl E.norm1_k)
        unfold toPP_k; omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [PPoly.denote_append, hEc.1, sp.1, denote_toPP_k _ B hB e he] at heq
  rw [Expr.denote_eq_denoteF, heq]; congr 1; rw [intCast_natCast]

namespace Stepwise

/-- The checks of the Kronecker certificates of `grind`'s steps: degrees below `B`, coefficients below `2 ^ K`. -/
noncomputable def kronOk_k (K B c : Nat) (p₁ p : Poly) (E : PPoly) (ls : KList) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.blt (Nat.mul 2 (Nat.add (Nat.add (Nat.add p.norm1_k p₁.norm1_k) ls.norm_k) (Nat.mul c E.norm1_k))) (Nat.pow 2 K))
    (ls.ok_k B)) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B)

theorem of_kronOk_k {K B c : Nat} {p₁ p : Poly} {E : PPoly} {ls : KList} (h : kronOk_k K B c p₁ p E ls = true) :
    (1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ ls.ok_k B = true) ∧
    2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K := by
  unfold kronOk_k at h
  have h₁ := PPoly.and_of_rec h
  have h₂ := PPoly.and_of_rec h₁.2
  have h₃ := PPoly.and_of_rec h₂.2
  have h₄ := PPoly.and_of_rec h₃.2
  exact ⟨⟨Nat.blt_eq.mp h₁.1, Nat.blt_eq.mp h₂.1, Nat.blt_eq.mp h₃.1, h₄.1⟩, Nat.blt_eq.mp h₄.2⟩

theorem simpsK {α} [CommRing α] (ctx : Context α) (K B : Nat) (p₁ p : Poly) (ls : KList)
    (hB : kronOk_k K B 0 p₁ p (.num 0) ls = true) (h : Int.beq' (p.kron_k K B) (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) = true) :
    ls.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B 0 p₁ p (.num 0) ls hB.1 hB.2 (by rw [h, Int.add_k_eq]; simp) hz, h₁]
  simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem simpsKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (p₁ p : Poly) (E : PPoly) (ls : KList)
    (hB : kronOk_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true) :
    ls.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B c p₁ p E ls hB.1 hB.2 (by rw [h, Int.add_k_eq, Int.add_k_eq, Int.mul_k_eq]; rfl) hz, h₁,
    (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

theorem d_stepsK {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (K B : Nat) (p₁ p : Poly) (ls : KList)
    (hB : kronOk_k K B 0 p₁ p (.num 0) ls = true) (h : Int.beq' (p.kron_k K B) (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) = true) :
    ls.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B 0 p₁ p (.num 0) ls hB.1 hB.2 (by rw [h, Int.add_k_eq]; simp) hz, h₁]
  simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem d_stepsKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (K B : Nat) (p₁ p : Poly) (E : PPoly) (ls : KList)
    (hB : kronOk_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true) :
    ls.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B c p₁ p E ls hB.1 hB.2 (by rw [h, Int.add_k_eq, Int.add_k_eq, Int.mul_k_eq]; rfl) hz, h₁,
    (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

/-- `kronOk_k`, `simpsK` and `d_stepsK` for multiples grouped by polynomial (`MList`). -/
noncomputable def kronOkM_k (K B c : Nat) (p₁ p : Poly) (E : PPoly) (ls : MList) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.blt (Nat.mul 2 (Nat.add (Nat.add (Nat.add p.norm1_k p₁.norm1_k) ls.norm_k) (Nat.mul c E.norm1_k))) (Nat.pow 2 K))
    (ls.ok_k B)) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B)

theorem of_kronOkM_k {K B c : Nat} {p₁ p : Poly} {E : PPoly} {ls : MList} (h : kronOkM_k K B c p₁ p E ls = true) :
    (1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ ls.ok_k B = true) ∧
    2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K := by
  unfold kronOkM_k at h
  have h₁ := PPoly.and_of_rec h
  have h₂ := PPoly.and_of_rec h₁.2
  have h₃ := PPoly.and_of_rec h₂.2
  have h₄ := PPoly.and_of_rec h₃.2
  exact ⟨⟨Nat.blt_eq.mp h₁.1, Nat.blt_eq.mp h₂.1, Nat.blt_eq.mp h₃.1, h₄.1⟩, Nat.blt_eq.mp h₄.2⟩

theorem simpsM {α} [CommRing α] (ctx : Context α) (K B : Nat) (p₁ p : Poly) (ls : MList)
    (hB : kronOkM_k K B 0 p₁ p (.num 0) ls = true) (h : Int.beq' (p.kron_k K B) (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) = true) :
    ls.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro hz h₁
  have hB := of_kronOkM_k hB
  rw [Int.beq'_eq] at h
  rw [MList.denote_eq ctx K B 0 p₁ p (.num 0) ls hB.1 hB.2 (by rw [h, Int.add_k_eq]; simp) hz, h₁]
  simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem simpsMC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (p₁ p : Poly) (E : PPoly) (ls : MList)
    (hB : kronOkM_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true) :
    ls.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro hz h₁
  have hB := of_kronOkM_k hB
  rw [Int.beq'_eq] at h
  rw [MList.denote_eq ctx K B c p₁ p E ls hB.1 hB.2 (by rw [h, Int.add_k_eq, Int.add_k_eq, Int.mul_k_eq]; rfl) hz, h₁,
    (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

theorem d_stepsM {α} [CommRing α] (ctx : Context α) (k : Int) (init : Poly) (K B : Nat) (p₁ p : Poly) (ls : MList)
    (hB : kronOkM_k K B 0 p₁ p (.num 0) ls = true) (h : Int.beq' (p.kron_k K B) (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) = true) :
    ls.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro hz h₁
  have hB := of_kronOkM_k hB
  rw [Int.beq'_eq] at h
  rw [MList.denote_eq ctx K B 0 p₁ p (.num 0) ls hB.1 hB.2 (by rw [h, Int.add_k_eq]; simp) hz, h₁]
  simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem d_stepsMC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (K B : Nat) (p₁ p : Poly) (E : PPoly) (ls : MList)
    (hB : kronOkM_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true) :
    ls.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro hz h₁
  have hB := of_kronOkM_k hB
  rw [Int.beq'_eq] at h
  rw [MList.denote_eq ctx K B c p₁ p E ls hB.1 hB.2 (by rw [h, Int.add_k_eq, Int.add_k_eq, Int.mul_k_eq]; rfl) hz, h₁,
    (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

/-- The checks of the Kronecker certificates of `grind`'s implications. -/
noncomputable def impOk_k (K B c : Nat) (e : Expr) (p : Poly) (E : PPoly) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.blt (Nat.mul 2 (Nat.add (Nat.add e.majorant_k p.norm1_k) (Nat.mul c E.norm1_k))) (Nat.pow 2 K))
    (Nat.blt p.maxDeg_k B)) (Nat.blt e.degB_k B)) (Nat.blt 1 B)

theorem of_impOk_k {K B c : Nat} {e : Expr} {p : Poly} {E : PPoly} (h : impOk_k K B c e p E = true) :
    (1 < B ∧ e.degB_k < B ∧ p.maxDeg_k < B) ∧ 2 * (e.majorant_k + p.norm1_k + c * E.norm1_k) < 2 ^ K := by
  unfold impOk_k at h
  have h₁ := PPoly.and_of_rec h
  have h₂ := PPoly.and_of_rec h₁.2
  have h₃ := PPoly.and_of_rec h₂.2
  exact ⟨⟨Nat.blt_eq.mp h₁.1, Nat.blt_eq.mp h₂.1, Nat.blt_eq.mp h₃.1⟩, Nat.blt_eq.mp h₃.2⟩

theorem imp_1eqK {α} [CommRing α] (ctx : Context α) (K B : Nat) (lhs rhs : Expr) (p₁ p₂ : Poly)
    (hB : impOk_k K B 0 (lhs.sub rhs) p₁ (.num 0) = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (p₁.kron_k K B) = true) (hp₂ : p₂ = .num 0) :
    (1 : Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B 0 (lhs.sub rhs) p₁ (.num 0) hB.1 hB.2 (by rw [h]; simp)
  subst hp₂
  rw [intCast_one, one_mul] at h₁
  rw [← sub_eq_zero_iff]
  show (lhs.sub rhs).denote ctx = 0
  rw [this, h₁]; simp [Poly.denote, Semiring.natCast_zero, zero_mul, add_zero, intCast_zero]

theorem imp_1eqKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (lhs rhs : Expr) (p₁ p₂ : Poly) (E : PPoly)
    (hB : impOk_k K B c (lhs.sub rhs) p₁ E = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (Int.add_k (p₁.kron_k K B) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true)
    (hp₂ : p₂ = .num 0) :
    (1 : Int) * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq, Int.add_k_eq, Int.mul_k_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B c (lhs.sub rhs) p₁ E hB.1 hB.2 h
  subst hp₂
  rw [intCast_one, one_mul] at h₁
  rw [← sub_eq_zero_iff]
  show (lhs.sub rhs).denote ctx = 0
  rw [this, h₁, (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]
  exact intCast_zero

/-- The input step `lhs = rhs` of `grind`'s ring solver, with `p` the polynomial of `lhs - rhs`, by Kronecker substitution. -/
theorem coreK {α} [CommRing α] (ctx : Context α) (K B : Nat) (lhs rhs : Expr) (p : Poly)
    (hB : impOk_k K B 0 (lhs.sub rhs) p (.num 0) = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (p.kron_k K B) = true) :
    lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B 0 (lhs.sub rhs) p (.num 0) hB.1 hB.2 (by rw [h]; simp)
  rw [Semiring.natCast_zero, zero_mul, add_zero] at this
  rw [← this]; exact sub_eq_zero_iff.mpr h₁

theorem coreKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (lhs rhs : Expr) (p : Poly) (E : PPoly)
    (hB : impOk_k K B c (lhs.sub rhs) p E = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (Int.add_k (p.kron_k K B) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true) :
    lhs.denote ctx = rhs.denote ctx → p.denote ctx = 0 := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq, Int.add_k_eq, Int.mul_k_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B c (lhs.sub rhs) p E hB.1 hB.2 h
  rw [(IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero] at this
  rw [← this]; exact sub_eq_zero_iff.mpr h₁

theorem imp_keqK {α} [CommRing α] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (K B : Nat) (lhs rhs : Expr) (p₁ p₂ : Poly)
    (hk : Int.beq' k 0 = false) (hB : impOk_k K B 0 (lhs.sub rhs) p₁ (.num 0) = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (p₁.kron_k K B) = true) (hp₂ : p₂ = .num 0) :
    k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B 0 (lhs.sub rhs) p₁ (.num 0) hB.1 hB.2 (by rw [h]; simp)
  subst hp₂
  have hk : k ≠ 0 := by simpa using hk
  rw [← zsmul_eq_intCast_mul] at h₁
  replace h₁ := no_int_zero_divisors hk (by rw [h₁]; exact intCast_zero)
  rw [← sub_eq_zero_iff]
  show (lhs.sub rhs).denote ctx = 0
  rw [this, h₁]; simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem imp_keqKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (K B : Nat) (lhs rhs : Expr)
    (p₁ p₂ : Poly) (E : PPoly) (hk : Int.beq' k 0 = false) (hB : impOk_k K B c (lhs.sub rhs) p₁ E = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (Int.add_k (p₁.kron_k K B) (Int.mul_k (Int.ofNat c) (E.kron_k K))) = true)
    (hp₂ : p₂ = .num 0) :
    k * p₁.denote ctx = p₂.denote ctx → lhs.denote ctx = rhs.denote ctx := by
  intro h₁
  have hB := of_impOk_k hB
  rw [Int.beq'_eq, Int.add_k_eq, Int.mul_k_eq] at h
  have := Expr.denote_eq_of_kron_poly ctx K B c (lhs.sub rhs) p₁ E hB.1 hB.2 h
  subst hp₂
  have hk : k ≠ 0 := by simpa using hk
  rw [← zsmul_eq_intCast_mul] at h₁
  replace h₁ := no_int_zero_divisors hk (by rw [h₁]; exact intCast_zero)
  rw [← sub_eq_zero_iff]
  show (lhs.sub rhs).denote ctx = 0
  rw [this, h₁, (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

end Stepwise

/-!
Field identities with inverses of numerals (`Expr.eq_of_kronQ`). With the variables of `invs`
denoting `1 / c`, an expression `e` is `num / den` for an integer polynomial `num`
(`Expr.toPPQ`, only used in proofs). The kernel computes the value of `num` at the point and `den`
(`Expr.kronQ_k`), so `a = b` follows from `num_a * den_b = num_b * den_a` at the point, with a
bound on the coefficients (`Expr.majQ_k`).
-/

/-- `invs.lookup x` for kernel reduction. -/
noncomputable def InvVars.lookup_k (invs : InvVars) (x : Var) : Option Nat :=
  List.rec none (fun p _ ih => Bool.rec ih (some p.2) (Nat.beq p.1 x)) invs

/-- `true` if the numerals of `invs` are not `0`. -/
noncomputable def InvVars.nonzero_k (invs : InvVars) : Bool :=
  List.rec true (fun p _ ih => Bool.rec false ih (Nat.blt 0 p.2)) invs

theorem InvVars.lookup_k_spec {α} [Field α] (ctx : Context α) (invs : InvVars) (hok : invs.ok ctx)
    (hnz : InvVars.nonzero_k invs = true) (x : Var) (c : Nat) (h : InvVars.lookup_k invs x = some c) :
    Var.denote ctx x = (c : α)⁻¹ ∧ c ≠ 0 := by
  induction invs with
  | nil => cases h
  | cons p invs ih =>
    obtain ⟨y, c'⟩ := p
    rw [InvVars.ok_cons] at hok
    have hnz : Bool.rec false (InvVars.nonzero_k invs) (Nat.blt 0 c') = true := hnz
    have hnz := PPoly.and_of_rec hnz
    have h : Bool.rec (InvVars.lookup_k invs x) (some c') (Nat.beq y x) = some c := h
    cases hyx : Nat.beq y x
    · rw [hyx] at h; exact ih hok.2 hnz.2 h
    · rw [hyx] at h
      cases h
      have : y = x := Nat.eq_of_beq_eq_true hyx
      subst this
      refine ⟨by rw [hok.1, Semiring.ofNat_eq_natCast], ?_⟩
      have := Nat.blt_eq.mp hnz.1; omega

/-- `Expr.degB_k`, where the variables of `invs` are constants. -/
noncomputable def Expr.degQB_k (invs : InvVars) (e : Expr) : Nat :=
  Expr.rec (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun x => Option.rec 1 (fun _ => 0) (InvVars.lookup_k invs x)) (fun _ ih => ih)
    (fun _ _ ih₁ ih₂ => Bool.rec ih₁ ih₂ (Nat.blt ih₁ ih₂))
    (fun _ _ ih₁ ih₂ => Bool.rec ih₁ ih₂ (Nat.blt ih₁ ih₂))
    (fun _ _ ih₁ ih₂ => Nat.add ih₁ ih₂)
    (fun _ k ih => Nat.mul ih k)
    e

/-- Checks the degree bound of `a` and `b` for the base `B`, where the variables of `invs` are constants. -/
noncomputable def Expr.degQOk_k (B : Nat) (invs : InvVars) (a b : Expr) : Bool :=
  Bool.rec false (Bool.rec false (Nat.blt (b.degQB_k invs) B) (Nat.blt (a.degQB_k invs) B)) (Nat.blt 1 B)

theorem Expr.of_degQOk_k {B : Nat} {invs : InvVars} {a b : Expr} (h : degQOk_k B invs a b = true) :
    1 < B ∧ a.degQB_k invs < B ∧ b.degQB_k invs < B := by
  unfold degQOk_k at h
  cases h₁ : Nat.blt 1 B <;> rw [h₁] at h
  · cases h
  · cases h₂ : Nat.blt (a.degQB_k invs) B <;> rw [h₂] at h
    · cases h
    · exact ⟨Nat.blt_eq.mp h₁, Nat.blt_eq.mp h₂, Nat.blt_eq.mp h⟩

/-- `(num, den)` of `e`, where the variables of `invs` are the constants `1 / c` (only used in proofs). -/
noncomputable def Expr.toPPQ (B : Nat) (invs : InvVars) : Expr → PPoly × Nat
  | .num k | .intCast k => (.num k, 1)
  | .natCast n => (.num n, 1)
  | .var x => match InvVars.lookup_k invs x with
    | some c => (.num 1, c)
    | none => (.add 1 1 (Nat.pow B x) (.num 0), 1)
  | .neg a => ((toPPQ B invs a).1.mulConst_k (-1), (toPPQ B invs a).2)
  | .add a b => (((toPPQ B invs a).1.mulConst_k (toPPQ B invs b).2).combine_k ((toPPQ B invs b).1.mulConst_k (toPPQ B invs a).2),
      (toPPQ B invs a).2 * (toPPQ B invs b).2)
  | .sub a b => (((toPPQ B invs a).1.mulConst_k (toPPQ B invs b).2).combine_k ((toPPQ B invs b).1.mulConst_k (-((toPPQ B invs a).2 : Int))),
      (toPPQ B invs a).2 * (toPPQ B invs b).2)
  | .mul a b => ((toPPQ B invs a).1.mulB_k (toPPQ B invs b).1, (toPPQ B invs a).2 * (toPPQ B invs b).2)
  | .pow a k => ((toPPQ B invs a).1.powB_k k, (toPPQ B invs a).2 ^ k)

/-- The value of the numerator of `e` at the point `xᵢ = (2 ^ K) ^ (B ^ i)`, and its denominator. -/
noncomputable def Expr.kronQ_k (K B : Nat) (invs : InvVars) (e : Expr) : Int × Nat :=
  Expr.rec (motive := fun _ => Int × Nat)
    (fun k => (k, 1)) (fun n => (Int.ofNat n, 1)) (fun k => (k, 1))
    (fun x => Option.rec (Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.pow B x))), 1) (fun c => (Int.ofNat 1, c)) (InvVars.lookup_k invs x))
    (fun _ ih => (Int.neg_k ih.1, ih.2))
    (fun _ _ ih₁ ih₂ => (Int.add_k (Int.mul_k ih₁.1 (Int.ofNat ih₂.2)) (Int.mul_k ih₂.1 (Int.ofNat ih₁.2)), Nat.mul ih₁.2 ih₂.2))
    (fun _ _ ih₁ ih₂ => (Int.sub_k (Int.mul_k ih₁.1 (Int.ofNat ih₂.2)) (Int.mul_k ih₂.1 (Int.ofNat ih₁.2)), Nat.mul ih₁.2 ih₂.2))
    (fun _ _ ih₁ ih₂ => (Int.mul_k ih₁.1 ih₂.1, Nat.mul ih₁.2 ih₂.2))
    (fun _ k ih => (Int.pow_k ih.1 k, Nat.pow ih.2 k)) e

/-- A bound on the coefficients of the numerator of `e`, and its denominator. -/
noncomputable def Expr.majQ_k (invs : InvVars) (e : Expr) : Nat × Nat :=
  Expr.rec (motive := fun _ => Nat × Nat)
    (fun k => (Int.natAbs_k k, 1)) (fun n => (n, 1)) (fun k => (Int.natAbs_k k, 1))
    (fun x => Option.rec (1, 1) (fun c => (1, c)) (InvVars.lookup_k invs x))
    (fun _ ih => ih)
    (fun _ _ ih₁ ih₂ => (Nat.add (Nat.mul ih₁.1 ih₂.2) (Nat.mul ih₂.1 ih₁.2), Nat.mul ih₁.2 ih₂.2))
    (fun _ _ ih₁ ih₂ => (Nat.add (Nat.mul ih₁.1 ih₂.2) (Nat.mul ih₂.1 ih₁.2), Nat.mul ih₁.2 ih₂.2))
    (fun _ _ ih₁ ih₂ => (Nat.mul ih₁.1 ih₂.1, Nat.mul ih₁.2 ih₂.2))
    (fun _ k ih => (Nat.pow ih.1 k, Nat.pow ih.2 k)) e

theorem PPoly.kron_combine_k (X : Int) {B : Nat} (hB : 1 < B) (p q : PPoly) :
    (p.combine_k q).kron X = p.kron X + q.kron X := by
  rw [← denote_kron X hB, ← denote_kron X hB, ← denote_kron X hB, (combine_k_spec _ B 0 p q).1]

theorem Expr.toPPQ_spec {α} [Field α] [IsCharP α 0] (f : Nat → α) (K B : Nat) (hB : 1 < B) (invs : InvVars)
    (hf : ∀ x c, InvVars.lookup_k invs x = some c → f x = (c : α)⁻¹ ∧ c ≠ 0) (e : Expr) (he : e.degQB_k invs < B) :
    (e.toPPQ B invs).1.denote f B = ((e.toPPQ B invs).2 : α) * e.denoteF f ∧
    (e.toPPQ B invs).1.Deg B (e.degQB_k invs) ∧ (e.toPPQ B invs).2 ≠ 0 ∧
    (e.toPPQ B invs).1.kron (2 ^ K) = (e.kronQ_k K B invs).1 ∧ (e.toPPQ B invs).2 = (e.kronQ_k K B invs).2 ∧
    (e.toPPQ B invs).1.norm1 ≤ (e.majQ_k invs).1 ∧ (e.toPPQ B invs).2 = (e.majQ_k invs).2 := by
  induction e with
  | num k =>
    refine ⟨?_, trivial, Nat.one_ne_zero, rfl, rfl, ?_, rfl⟩
    · show (k : α) = ((1 : Nat) : α) * denoteInt k; rw [denoteInt_eq, Semiring.natCast_one, one_mul]
    · show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | natCast n =>
    refine ⟨?_, trivial, Nat.one_ne_zero, rfl, rfl, ?_, rfl⟩
    · show ((n : Int) : α) = ((1 : Nat) : α) * NatCast.natCast n; rw [Semiring.natCast_one, one_mul, intCast_natCast]
    · show (n : Int).natAbs ≤ n; simp
  | intCast k =>
    refine ⟨?_, trivial, Nat.one_ne_zero, rfl, rfl, ?_, rfl⟩
    · show (k : α) = ((1 : Nat) : α) * IntCast.intCast k; rw [Semiring.natCast_one, one_mul]
    · show k.natAbs ≤ Int.natAbs_k k; rw [Int.natAbs_k_eq]; exact Nat.le_refl _
  | var x =>
    cases hx : InvVars.lookup_k invs x with
    | some c =>
      have hc := hf x c hx
      have e₁ : (Expr.var x).toPPQ B invs = (.num 1, c) := by simp only [toPPQ, hx]
      have e₂ : (Expr.var x).kronQ_k K B invs = (Int.ofNat 1, c) := by
        show Option.rec (motive := fun _ => Int × Nat) (Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.pow B x))), 1) (fun c => (Int.ofNat 1, c))
          (InvVars.lookup_k invs x) = _
        rw [hx]
      have e₃ : (Expr.var x).majQ_k invs = (1, c) := by
        show Option.rec (motive := fun _ => Nat × Nat) (1, 1) (fun c => (1, c)) (InvVars.lookup_k invs x) = _
        rw [hx]
      have e₄ : (Expr.var x).degQB_k invs = 0 := by
        show Option.rec (motive := fun _ => Nat) 1 (fun _ => 0) (InvVars.lookup_k invs x) = _
        rw [hx]
      rw [e₁, e₂, e₃, e₄]
      refine ⟨?_, trivial, hc.2, rfl, rfl, Nat.le_refl _, rfl⟩
      show ((1 : Int) : α) = (c : α) * f x
      rw [hc.1, intCast_one, Field.mul_inv_cancel (Field.natCast_ne_zero hc.2)]
    | none =>
      have e₁ : (Expr.var x).toPPQ B invs = (.add 1 1 (Nat.pow B x) (.num 0), 1) := by simp only [toPPQ, hx]
      have e₂ : (Expr.var x).kronQ_k K B invs = (Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.pow B x))), 1) := by
        show Option.rec (motive := fun _ => Int × Nat) (Int.ofNat (Nat.pow 2 (Nat.mul K (Nat.pow B x))), 1) (fun c => (Int.ofNat 1, c))
          (InvVars.lookup_k invs x) = _
        rw [hx]
      have e₃ : (Expr.var x).majQ_k invs = (1, 1) := by
        show Option.rec (motive := fun _ => Nat × Nat) (1, 1) (fun c => (1, c)) (InvVars.lookup_k invs x) = _
        rw [hx]
      have e₄ : (Expr.var x).degQB_k invs = 1 := by
        show Option.rec (motive := fun _ => Nat) 1 (fun _ => 0) (InvVars.lookup_k invs x) = _
        rw [hx]
      rw [e₁, e₂, e₃, e₄]
      have hx1 : PPoly.dsum B (Nat.pow B x) = 1 := by
        have := PPoly.dsum_mul_pow hB x 1 hB; rwa [Nat.one_mul] at this
      have hm := PPoly.monDenote_mul_pow f hB 0 x 1 hB
      rw [Nat.one_mul] at hm
      refine ⟨?_, ⟨by rw [hx1]; exact Nat.le_refl _, trivial⟩, Nat.one_ne_zero, ?_, rfl, by simp [PPoly.norm1], rfl⟩
      · show ((1 : Int) : α) * PPoly.monDenote f B 0 (Nat.pow B x) + ((0 : Int) : α) = ((1 : Nat) : α) * f x
        rw [show Nat.pow B x = B ^ x from rfl, hm, Nat.zero_add, pow_one, intCast_one, one_mul, intCast_zero, add_zero,
          Semiring.natCast_one, one_mul]
      · show (1 : Int) * (2 ^ K) ^ Nat.pow B x + 0 = Int.ofNat (2 ^ (K * B ^ x))
        rw [Int.one_mul, Int.add_zero, ← Int.pow_mul]; exact (Int.natCast_pow 2 _).symm
  | neg a ih =>
    have ih := ih he
    obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := ih
    have hm := PPoly.mulConst_k_spec f B (a.degQB_k invs) (-1) (a.toPPQ B invs).1
    refine ⟨?_, hm.2 h₂, h₃, ?_, h₅, ?_, h₇⟩
    · show ((a.toPPQ B invs).1.mulConst_k (-1)).denote f B = _ * - a.denoteF f
      rw [hm.1, h₁, intCast_neg_one, ← neg_eq_neg_one_mul, mul_neg]; rfl
    · show ((a.toPPQ B invs).1.mulConst_k (-1)).kron _ = Int.neg_k (a.kronQ_k K B invs).1
      rw [PPoly.kron_mulConst_k, h₄, Int.neg_k_eq]; show -1 * _ = -_; omega
    · show ((a.toPPQ B invs).1.mulConst_k (-1)).norm1 ≤ (a.majQ_k invs).1
      have := PPoly.norm1_mulConst_k (-1) (a.toPPQ B invs).1
      simp at this; omega
  | add a b iha ihb =>
    have hm := Expr.le_max_k (a.degQB_k invs) (b.degQB_k invs)
    have he' : Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) < B := he
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := iha (by omega)
    obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := ihb (by omega)
    have mp := PPoly.mulConst_k_spec f B (a.degQB_k invs) (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
    have mq := PPoly.mulConst_k_spec f B (b.degQB_k invs) (((a.toPPQ B invs).2) : Int) ((b.toPPQ B invs).1)
    have hD : (Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) : Nat) = ((Expr.add a b).degQB_k invs) := rfl
    have hc := PPoly.combine_k_spec f B ((Expr.add a b).degQB_k invs) (((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)) (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))
    refine ⟨?_, hc.2 (PPoly.Deg.mono (by rw [← hD]; exact hm.1) _ (mp.2 a₂)) (PPoly.Deg.mono (by rw [← hD]; exact hm.2) _ (mq.2 b₂)),
      Nat.mul_ne_zero a₃ b₃, ?_, ?_, ?_, ?_⟩
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))).denote f B = ((((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) : Nat) : α) * (a.denoteF f + b.denoteF f)
      rw [hc.1, mp.1, mq.1, a₁, b₁, Semiring.natCast_mul, left_distrib, intCast_natCast, intCast_natCast]
      simp only [mul_assoc, mul_left_comm]
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))).kron _ =
        Int.add_k (Int.mul_k (a.kronQ_k K B invs).1 (Int.ofNat (b.kronQ_k K B invs).2)) (Int.mul_k (b.kronQ_k K B invs).1 (Int.ofNat (a.kronQ_k K B invs).2))
      rw [PPoly.kron_combine_k _ hB, PPoly.kron_mulConst_k, PPoly.kron_mulConst_k, a₄, b₄, ← a₅, ← b₅, Int.add_k_eq, Int.mul_k_eq, Int.mul_k_eq]
      show (((b.toPPQ B invs).2) : Int) * _ + (((a.toPPQ B invs).2) : Int) * _ = _ * (((b.toPPQ B invs).2) : Int) + _ * (((a.toPPQ B invs).2) : Int)
      rw [Int.mul_comm (((b.toPPQ B invs).2) : Int), Int.mul_comm (((a.toPPQ B invs).2) : Int)]
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.kronQ_k K B invs).2 (b.kronQ_k K B invs).2; rw [← a₅, ← b₅]; rfl
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))).norm1 ≤
        Nat.add (Nat.mul (a.majQ_k invs).1 (b.majQ_k invs).2) (Nat.mul (b.majQ_k invs).1 (a.majQ_k invs).2)
      have := PPoly.norm1_combine_k (((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)) (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))
      have := PPoly.norm1_mulConst_k (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
      have := PPoly.norm1_mulConst_k (((a.toPPQ B invs).2) : Int) ((b.toPPQ B invs).1)
      rw [← a₇, ← b₇, Nat.add_eq, Nat.mul_eq, Nat.mul_eq]
      rw [show ((((b.toPPQ B invs).2) : Int)).natAbs = ((b.toPPQ B invs).2) from rfl] at *
      rw [show ((((a.toPPQ B invs).2) : Int)).natAbs = ((a.toPPQ B invs).2) from rfl] at *
      have := Nat.mul_le_mul_left ((b.toPPQ B invs).2) a₆
      have := Nat.mul_le_mul_left ((a.toPPQ B invs).2) b₆
      rw [Nat.mul_comm (a.majQ_k invs).1, Nat.mul_comm (b.majQ_k invs).1]
      omega
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.majQ_k invs).2 (b.majQ_k invs).2; rw [← a₇, ← b₇]; rfl
  | sub a b iha ihb =>
    have hm := Expr.le_max_k (a.degQB_k invs) (b.degQB_k invs)
    have he' : Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) < B := he
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := iha (by omega)
    obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := ihb (by omega)
    have mp := PPoly.mulConst_k_spec f B (a.degQB_k invs) (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
    have mq := PPoly.mulConst_k_spec f B (b.degQB_k invs) (-(((a.toPPQ B invs).2) : Int)) ((b.toPPQ B invs).1)
    have hD : (Bool.rec (a.degQB_k invs) (b.degQB_k invs) (Nat.blt (a.degQB_k invs) (b.degQB_k invs)) : Nat) = ((Expr.sub a b).degQB_k invs) := rfl
    have hc := PPoly.combine_k_spec f B ((Expr.sub a b).degQB_k invs) (((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)) (((b.toPPQ B invs).1).mulConst_k (-(((a.toPPQ B invs).2) : Int)))
    refine ⟨?_, hc.2 (PPoly.Deg.mono (by rw [← hD]; exact hm.1) _ (mp.2 a₂)) (PPoly.Deg.mono (by rw [← hD]; exact hm.2) _ (mq.2 b₂)),
      Nat.mul_ne_zero a₃ b₃, ?_, ?_, ?_, ?_⟩
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k (-(((a.toPPQ B invs).2) : Int)))).denote f B = ((((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) : Nat) : α) * (a.denoteF f - b.denoteF f)
      rw [hc.1, mp.1, mq.1, a₁, b₁, Semiring.natCast_mul, sub_eq_add_neg, left_distrib, intCast_neg, intCast_natCast, intCast_natCast,
        neg_mul, mul_neg]
      simp only [mul_assoc, mul_left_comm]
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k (-(((a.toPPQ B invs).2) : Int)))).kron _ =
        Int.sub_k (Int.mul_k (a.kronQ_k K B invs).1 (Int.ofNat (b.kronQ_k K B invs).2)) (Int.mul_k (b.kronQ_k K B invs).1 (Int.ofNat (a.kronQ_k K B invs).2))
      rw [PPoly.kron_combine_k _ hB, PPoly.kron_mulConst_k, PPoly.kron_mulConst_k, a₄, b₄, ← a₅, ← b₅, Int.sub_k_eq, Int.mul_k_eq, Int.mul_k_eq]
      show (((b.toPPQ B invs).2) : Int) * _ + (-(((a.toPPQ B invs).2) : Int)) * _ = _ * (((b.toPPQ B invs).2) : Int) - _ * (((a.toPPQ B invs).2) : Int)
      rw [Int.mul_comm (((b.toPPQ B invs).2) : Int), Int.neg_mul, Int.mul_comm (((a.toPPQ B invs).2) : Int)]; omega
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.kronQ_k K B invs).2 (b.kronQ_k K B invs).2; rw [← a₅, ← b₅]; rfl
    · show ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).combine_k (((b.toPPQ B invs).1).mulConst_k (-(((a.toPPQ B invs).2) : Int)))).norm1 ≤
        Nat.add (Nat.mul (a.majQ_k invs).1 (b.majQ_k invs).2) (Nat.mul (b.majQ_k invs).1 (a.majQ_k invs).2)
      have := PPoly.norm1_combine_k (((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)) (((b.toPPQ B invs).1).mulConst_k (-(((a.toPPQ B invs).2) : Int)))
      have := PPoly.norm1_mulConst_k (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
      have := PPoly.norm1_mulConst_k (-(((a.toPPQ B invs).2) : Int)) ((b.toPPQ B invs).1)
      rw [← a₇, ← b₇, Nat.add_eq, Nat.mul_eq, Nat.mul_eq]
      rw [show ((((b.toPPQ B invs).2) : Int)).natAbs = ((b.toPPQ B invs).2) from rfl] at *
      rw [show (-(((a.toPPQ B invs).2) : Int)).natAbs = ((a.toPPQ B invs).2) by simp] at *
      have := Nat.mul_le_mul_left ((b.toPPQ B invs).2) a₆
      have := Nat.mul_le_mul_left ((a.toPPQ B invs).2) b₆
      rw [Nat.mul_comm (a.majQ_k invs).1, Nat.mul_comm (b.majQ_k invs).1]
      omega
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.majQ_k invs).2 (b.majQ_k invs).2; rw [← a₇, ← b₇]; rfl
  | mul a b iha ihb =>
    have he' : Nat.add (a.degQB_k invs) (b.degQB_k invs) < B := he
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := iha (by simp at he'; omega)
    obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := ihb (by simp at he'; omega)
    have hp := PPoly.mulB_k_spec f B (a.degQB_k invs) (b.degQB_k invs) hB (by simp at he'; omega) ((a.toPPQ B invs).1) ((b.toPPQ B invs).1) a₂ b₂
    have hpI := PPoly.mulB_k_spec (fun i => ((2 : Int) ^ K) ^ (B ^ i)) B (a.degQB_k invs) (b.degQB_k invs) hB (by simp at he'; omega) ((a.toPPQ B invs).1) ((b.toPPQ B invs).1) a₂ b₂
    refine ⟨?_, hp.2, Nat.mul_ne_zero a₃ b₃, ?_, ?_, ?_, ?_⟩
    · show (((a.toPPQ B invs).1).mulB_k ((b.toPPQ B invs).1)).denote f B = ((((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) : Nat) : α) * (a.denoteF f * b.denoteF f)
      rw [hp.1, a₁, b₁, Semiring.natCast_mul]; simp only [mul_assoc, mul_left_comm]
    · show (((a.toPPQ B invs).1).mulB_k ((b.toPPQ B invs).1)).kron _ = Int.mul_k (a.kronQ_k K B invs).1 (b.kronQ_k K B invs).1
      rw [← PPoly.denote_kron _ hB, hpI.1, PPoly.denote_kron _ hB, PPoly.denote_kron _ hB, a₄, b₄, Int.mul_k_eq]; rfl
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.kronQ_k K B invs).2 (b.kronQ_k K B invs).2; rw [← a₅, ← b₅]; rfl
    · show (((a.toPPQ B invs).1).mulB_k ((b.toPPQ B invs).1)).norm1 ≤ Nat.mul (a.majQ_k invs).1 (b.majQ_k invs).1
      exact Nat.le_trans (PPoly.norm1_mulB_k ((a.toPPQ B invs).1) ((b.toPPQ B invs).1)) (Nat.mul_le_mul a₆ b₆)
    · show ((a.toPPQ B invs).2) * ((b.toPPQ B invs).2) = Nat.mul (a.majQ_k invs).2 (b.majQ_k invs).2; rw [← a₇, ← b₇]; rfl
  | pow a k ih =>
    by_cases hk : k = 0
    · subst hk
      refine ⟨?_, trivial, by show (a.toPPQ B invs).2 ^ 0 ≠ 0; simp, ?_, ?_, ?_, ?_⟩
      · show (((a.toPPQ B invs).1.powB_k 0).denote f B) = (((a.toPPQ B invs).2 ^ 0 : Nat) : α) * a.denoteF f ^ 0
        show ((Int.ofNat 1 : Int) : α) = _
        rw [Nat.pow_zero, pow_zero, Semiring.natCast_one, one_mul]; exact intCast_one
      · show ((a.toPPQ B invs).1.powB_k 0).kron _ = Int.pow_k (a.kronQ_k K B invs).1 0
        rw [Int.pow_k_eq, Int.pow_zero]; rfl
      · show (a.toPPQ B invs).2 ^ 0 = Nat.pow (a.kronQ_k K B invs).2 0; simp
      · show ((a.toPPQ B invs).1.powB_k 0).norm1 ≤ Nat.pow (a.majQ_k invs).1 0; simp [PPoly.powB_k, PPoly.norm1]
      · show (a.toPPQ B invs).2 ^ 0 = Nat.pow (a.majQ_k invs).2 0; simp
    have he' : Nat.mul (a.degQB_k invs) k < B := he
    have hk' : (a.degQB_k invs) ≤ (a.degQB_k invs) * k := Nat.le_mul_of_pos_right _ (by omega)
    obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := ih (by simp at he'; omega)
    have hp := PPoly.powB_k_spec f B (a.degQB_k invs) hB ((a.toPPQ B invs).1) k a₂ (by simp at he'; omega)
    have hpI := PPoly.powB_k_spec (fun i => ((2 : Int) ^ K) ^ (B ^ i)) B (a.degQB_k invs) hB ((a.toPPQ B invs).1) k a₂ (by simp at he'; omega)
    refine ⟨?_, hp.2, Nat.pos_iff_ne_zero.mp (Nat.pow_pos (Nat.pos_iff_ne_zero.mpr a₃)), ?_, ?_, ?_, ?_⟩
    · show (((a.toPPQ B invs).1).powB_k k).denote f B = ((((a.toPPQ B invs).2) ^ k : Nat) : α) * a.denoteF f ^ k
      rw [hp.1, a₁, Semiring.natCast_pow, mul_pow]
    · show (((a.toPPQ B invs).1).powB_k k).kron _ = Int.pow_k (a.kronQ_k K B invs).1 k
      rw [← PPoly.denote_kron _ hB, hpI.1, PPoly.denote_kron _ hB, a₄, Int.pow_k_eq]
    · show ((a.toPPQ B invs).2) ^ k = Nat.pow (a.kronQ_k K B invs).2 k; rw [← a₅]; rfl
    · show (((a.toPPQ B invs).1).powB_k k).norm1 ≤ Nat.pow (a.majQ_k invs).1 k
      exact Nat.le_trans (PPoly.norm1_powB_k ((a.toPPQ B invs).1) k) (Nat.pow_le_pow_left a₆ k)
    · show ((a.toPPQ B invs).2) ^ k = Nat.pow (a.majQ_k invs).2 k; rw [← a₇]; rfl

/-- Checks the bound on the coefficients of `num_a * den_b - num_b * den_a`. -/
noncomputable def Expr.kronQOk_k (K : Nat) (invs : InvVars) (a b : Expr) : Bool :=
  Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (b.majQ_k invs).2 (a.majQ_k invs).1) (Nat.mul (a.majQ_k invs).2 (b.majQ_k invs).1))) (Nat.pow 2 K)

/-- `num_a * den_b = num_b * den_a` at the point. -/
noncomputable def Expr.kronQEq_k (K B : Nat) (invs : InvVars) (a b : Expr) : Bool :=
  Int.beq' (Int.mul_k (a.kronQ_k K B invs).1 (Int.ofNat (b.kronQ_k K B invs).2))
    (Int.mul_k (b.kronQ_k K B invs).1 (Int.ofNat (a.kronQ_k K B invs).2))

theorem Expr.eq_of_kronQ {α} [Field α] [IsCharP α 0] (ctx : Context α) (K B : Nat) (invs : InvVars) (hok : invs.ok ctx)
    (hnz : InvVars.nonzero_k invs = true) (a b : Expr) (hB : degQOk_k B invs a b = true) (hK : kronQOk_k K invs a b = true)
    (h : kronQEq_k K B invs a b = true) : a.denote ctx = b.denote ctx := by
  have hB := of_degQOk_k hB
  have hf := InvVars.lookup_k_spec ctx invs hok hnz
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇⟩ := toPPQ_spec (Var.denote ctx) K B hB.1 invs hf a hB.2.1
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆, b₇⟩ := toPPQ_spec (Var.denote ctx) K B hB.1 invs hf b hB.2.2
  have hK : 2 * (((b.toPPQ B invs).2) * (a.majQ_k invs).1 + ((a.toPPQ B invs).2) * (b.majQ_k invs).1) < 2 ^ K := by
    have := Nat.blt_eq.mp hK; rw [← a₇, ← b₇] at this; simpa using this
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have mp := PPoly.mulConst_k_spec (Var.denote ctx) B 0 (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
  have mq := PPoly.mulConst_k_spec (Var.denote ctx) B 0 (((a.toPPQ B invs).2) : Int) ((b.toPPQ B invs).1)
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)) (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2))
    (by
      rw [PPoly.kron_mulConst_k, PPoly.kron_mulConst_k, a₄, b₄]
      have h := h; unfold kronQEq_k at h; rw [Int.beq'_eq, Int.mul_k_eq, Int.mul_k_eq, ← a₅, ← b₅] at h
      show (((b.toPPQ B invs).2) : Int) * _ = (((a.toPPQ B invs).2) : Int) * _
      rw [Int.mul_comm, Int.mul_comm (((a.toPPQ B invs).2) : Int)]; exact h)
    (by
      have := PPoly.norm1_mulConst_k (((b.toPPQ B invs).2) : Int) ((a.toPPQ B invs).1)
      have := PPoly.norm1_mulConst_k (((a.toPPQ B invs).2) : Int) ((b.toPPQ B invs).1)
      rw [show ((((b.toPPQ B invs).2) : Int)).natAbs = ((b.toPPQ B invs).2) from rfl] at *
      rw [show ((((a.toPPQ B invs).2) : Int)).natAbs = ((a.toPPQ B invs).2) from rfl] at *
      have := Nat.mul_le_mul_left ((b.toPPQ B invs).2) a₆
      have := Nat.mul_le_mul_left ((a.toPPQ B invs).2) b₆
      have : 2 * ((((a.toPPQ B invs).1).mulConst_k ((b.toPPQ B invs).2)).norm1 + (((b.toPPQ B invs).1).mulConst_k ((a.toPPQ B invs).2)).norm1) < 2 ^ K := by omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [mp.1, mq.1, a₁, b₁, intCast_natCast, intCast_natCast] at heq
  have hs : (((a.toPPQ B invs).2) : α) ≠ 0 := Field.natCast_ne_zero a₃
  have ht : (((b.toPPQ B invs).2) : α) ≠ 0 := Field.natCast_ne_zero b₃
  have : ((((b.toPPQ B invs).2) : α) * ((a.toPPQ B invs).2)) * (a.denoteF (Var.denote ctx) - b.denoteF (Var.denote ctx)) = 0 := by
    rw [sub_eq_add_neg, left_distrib, mul_neg, ← sub_eq_add_neg, AddCommGroup.sub_eq_zero_iff]
    calc (((b.toPPQ B invs).2) : α) * ((a.toPPQ B invs).2) * a.denoteF (Var.denote ctx)
        = (((b.toPPQ B invs).2) : α) * ((((a.toPPQ B invs).2) : α) * a.denoteF (Var.denote ctx)) := by rw [mul_assoc]
      _ = (((a.toPPQ B invs).2) : α) * ((((b.toPPQ B invs).2) : α) * b.denoteF (Var.denote ctx)) := heq
      _ = (((b.toPPQ B invs).2) : α) * ((a.toPPQ B invs).2) * b.denoteF (Var.denote ctx) := by
        rw [← mul_assoc, CommSemiring.mul_comm (((a.toPPQ B invs).2) : α)]
  rcases Field.of_mul_eq_zero this with h0 | h0
  · rcases Field.of_mul_eq_zero h0 with h1 | h1
    · exact absurd h1 ht
    · exact absurd h1 hs
  · rw [Expr.denote_eq_denoteF, Expr.denote_eq_denoteF]; exact AddCommGroup.sub_eq_zero_iff.mp h0

theorem eq_true_of_kronQ {α} [Field α] [IsCharP α 0] (ctx : Context α) (K B : Nat) (invs : InvVars) (hok : invs.ok ctx)
    (hnz : InvVars.nonzero_k invs = true) (a b : Expr) (hB : Expr.degQOk_k B invs a b = true) (hK : Expr.kronQOk_k K invs a b = true)
    (h : Expr.kronQEq_k K B invs a b = true) : (a.denote ctx = b.denote ctx) = True :=
  eq_true (Expr.eq_of_kronQ ctx K B invs hok hnz a b hB hK h)

/--
`lhs - rhs` is `lhs' - rhs'` divided by `d`, by Kronecker substitution: the normalization of a
relation with inverses of numerals, whose sides `lhs'` and `rhs'` have no denominators.
-/
theorem Expr.sub_mul_eq_of_kronQ {α} [Field α] [IsCharP α 0] (ctx : Context α) (K B : Nat) (invs : InvVars)
    (hok : invs.ok ctx) (hnz : InvVars.nonzero_k invs = true) (d : Nat) (lhs rhs lhs' rhs' : Expr)
    (hB : Expr.degQOk_k B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (hK : Expr.kronQOk_k K invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (h : Expr.kronQEq_k K B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true) :
    (lhs.denote ctx - rhs.denote ctx) * (d : α) = lhs'.denote ctx - rhs'.denote ctx := by
  have := Expr.eq_of_kronQ ctx K B invs hok hnz _ _ hB hK h
  have hd : denoteInt (α := α) (d : Int) = (d : α) := by rw [denoteInt_eq, Ring.intCast_natCast]
  rw [← hd]; exact this

theorem eq_of_kronQ_rel {α} [Field α] [IsCharP α 0] (ctx : Context α) (K B : Nat) (invs : InvVars)
    (hok : invs.ok ctx) (hnz : InvVars.nonzero_k invs = true) (d : Nat) (hd : Nat.blt 0 d = true) (lhs rhs lhs' rhs' : Expr)
    (hB : Expr.degQOk_k B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (hK : Expr.kronQOk_k K invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (h : Expr.kronQEq_k K B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true) :
    (lhs.denote ctx = rhs.denote ctx) = (lhs'.denote ctx = rhs'.denote ctx) := by
  have h := Expr.sub_mul_eq_of_kronQ ctx K B invs hok hnz d lhs rhs lhs' rhs' hB hK h
  have hd : (d : α) ≠ 0 := Field.natCast_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.blt_eq.mp hd))
  rw [← AddCommGroup.sub_eq_zero_iff (a := lhs.denote ctx) (b := rhs.denote ctx),
    ← AddCommGroup.sub_eq_zero_iff (a := lhs'.denote ctx) (b := rhs'.denote ctx), ← h]
  apply propext; constructor
  · intro h0; rw [h0, Semiring.zero_mul]
  · intro h0
    rcases Field.of_mul_eq_zero h0 with h0 | h0
    · exact h0
    · exact absurd h0 hd

private theorem sub_nonpos_iff' {α} [Ring α] [LE α] [IsPreorder α] [OrderedAdd α] {a b : α} : a - b ≤ 0 ↔ a ≤ b := by
  rw [← OrderedAdd.neg_nonneg_iff, AddCommGroup.neg_sub, OrderedAdd.sub_nonneg_iff]

private theorem sub_neg_iff' {α} [Ring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α} :
    a - b < 0 ↔ a < b := by
  rw [← OrderedAdd.neg_pos_iff, AddCommGroup.neg_sub, OrderedAdd.sub_pos_iff]

section
variable {α : Type u} [Field α] [IsCharP α 0] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

theorem le_of_kronQ_rel (ctx : Context α) (K B : Nat) (invs : InvVars)
    (hok : invs.ok ctx) (hnz : InvVars.nonzero_k invs = true) (d : Nat) (hd : Nat.blt 0 d = true) (lhs rhs lhs' rhs' : Expr)
    (hB : Expr.degQOk_k B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (hK : Expr.kronQOk_k K invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (h : Expr.kronQEq_k K B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true) :
    (lhs.denote ctx ≤ rhs.denote ctx) = (lhs'.denote ctx ≤ rhs'.denote ctx) := by
  have h := Expr.sub_mul_eq_of_kronQ ctx K B invs hok hnz d lhs rhs lhs' rhs' hB hK h
  have hd : (0 : α) < d := OrderedRing.pos_natCast_of_pos d (Nat.blt_eq.mp hd)
  have := Field.IsOrdered.mul_le_mul_iff_of_pos_right (a := lhs.denote ctx - rhs.denote ctx) (b := 0) hd
  rw [Semiring.zero_mul, h] at this
  rw [← sub_nonpos_iff', ← sub_nonpos_iff' (a := lhs'.denote ctx), this]

theorem lt_of_kronQ_rel (ctx : Context α) (K B : Nat) (invs : InvVars)
    (hok : invs.ok ctx) (hnz : InvVars.nonzero_k invs = true) (d : Nat) (hd : Nat.blt 0 d = true) (lhs rhs lhs' rhs' : Expr)
    (hB : Expr.degQOk_k B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (hK : Expr.kronQOk_k K invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true)
    (h : Expr.kronQEq_k K B invs ((lhs.sub rhs).mul (.num d)) (lhs'.sub rhs') = true) :
    (lhs.denote ctx < rhs.denote ctx) = (lhs'.denote ctx < rhs'.denote ctx) := by
  have h := Expr.sub_mul_eq_of_kronQ ctx K B invs hok hnz d lhs rhs lhs' rhs' hB hK h
  have hd : (0 : α) < d := OrderedRing.pos_natCast_of_pos d (Nat.blt_eq.mp hd)
  have := Field.IsOrdered.mul_lt_mul_iff_of_pos_right (a := lhs.denote ctx - rhs.denote ctx) (b := 0) hd
  rw [Semiring.zero_mul, h] at this
  rw [← sub_neg_iff', ← sub_neg_iff' (a := lhs'.denote ctx), this]

end


/-!
Relations `lhs ⋈ rhs` rewritten to `lhs' ⋈ rhs'` with `lhs - rhs` and `lhs' - rhs'` the same
polynomial, checked at a point (`le_of_kron_rel`, and `le_of_kronLin_rel` for linear terms over
many variables).
-/

theorem eq_of_kron_rel {α} [CommRing α] (ctx : Context α) (K B : Nat) (l r l' r' : Expr)
    (hB : Expr.degOk_k B (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronEval_k K B = (l'.sub r').kronEval_k K B) :
    (l.denote ctx = r.denote ctx) = (l'.denote ctx = r'.denote ctx) := by
  have h := Expr.eq_of_kron ctx K B _ _ hB hK h
  rw [← sub_eq_zero_iff (a := l.denote ctx), ← sub_eq_zero_iff (a := l'.denote ctx)]
  exact congrArg (· = 0) h

theorem eq_of_kronLin_rel {α} [CommRing α] (ctx : Context α) (K : Nat) (l r l' r' : Expr)
    (hl : Expr.linOk_k (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronLinEval_k K = (l'.sub r').kronLinEval_k K) :
    (l.denote ctx = r.denote ctx) = (l'.denote ctx = r'.denote ctx) := by
  have h := Expr.eq_of_kronLin ctx K _ _ hl hK h
  rw [← sub_eq_zero_iff (a := l.denote ctx), ← sub_eq_zero_iff (a := l'.denote ctx)]
  exact congrArg (· = 0) h

section
variable {α : Type u} [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α]

theorem le_of_kron_rel (ctx : Context α) (K B : Nat) (l r l' r' : Expr)
    (hB : Expr.degOk_k B (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronEval_k K B = (l'.sub r').kronEval_k K B) :
    (l.denote ctx ≤ r.denote ctx) = (l'.denote ctx ≤ r'.denote ctx) := by
  have h := Expr.eq_of_kron ctx K B _ _ hB hK h
  rw [← sub_nonpos_iff' (a := l.denote ctx), ← sub_nonpos_iff' (a := l'.denote ctx)]
  exact congrArg (· ≤ 0) h

theorem le_of_kronLin_rel (ctx : Context α) (K : Nat) (l r l' r' : Expr)
    (hl : Expr.linOk_k (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronLinEval_k K = (l'.sub r').kronLinEval_k K) :
    (l.denote ctx ≤ r.denote ctx) = (l'.denote ctx ≤ r'.denote ctx) := by
  have h := Expr.eq_of_kronLin ctx K _ _ hl hK h
  rw [← sub_nonpos_iff' (a := l.denote ctx), ← sub_nonpos_iff' (a := l'.denote ctx)]
  exact congrArg (· ≤ 0) h

theorem lt_of_kron_rel [LawfulOrderLT α] (ctx : Context α) (K B : Nat) (l r l' r' : Expr)
    (hB : Expr.degOk_k B (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronEval_k K B = (l'.sub r').kronEval_k K B) :
    (l.denote ctx < r.denote ctx) = (l'.denote ctx < r'.denote ctx) := by
  have h := Expr.eq_of_kron ctx K B _ _ hB hK h
  rw [← sub_neg_iff' (a := l.denote ctx), ← sub_neg_iff' (a := l'.denote ctx)]
  exact congrArg (· < 0) h

theorem lt_of_kronLin_rel [LawfulOrderLT α] (ctx : Context α) (K : Nat) (l r l' r' : Expr)
    (hl : Expr.linOk_k (l.sub r) (l'.sub r') = true) (hK : Expr.kronOk_k K (l.sub r) (l'.sub r') = true)
    (h : (l.sub r).kronLinEval_k K = (l'.sub r').kronLinEval_k K) :
    (l.denote ctx < r.denote ctx) = (l'.denote ctx < r'.denote ctx) := by
  have h := Expr.eq_of_kronLin ctx K _ _ hl hK h
  rw [← sub_neg_iff' (a := l.denote ctx), ← sub_neg_iff' (a := l'.denote ctx)]
  exact congrArg (· < 0) h

end

/-! `eq_cancel_of_kronS` and its variants for linear terms over many variables. -/

theorem eq_cancel_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K : Nat) (a b a' b' c : Expr)
    (hl₁ : Expr.linSOk_k a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronLinEval_k K = (a'.add c).kronLinEval_k K)
    (hl₂ : Expr.linSOk_k b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronLinEval_k K = (b'.add c).kronLinEval_k K) :
    (a.denoteS ctx = b.denoteS ctx) = (a'.denoteS ctx = b'.denoteS ctx) := by
  rw [Expr.eq_of_kronLinS ctx K a (a'.add c) hl₁ hK₁ h₁, Expr.eq_of_kronLinS ctx K b (b'.add c) hl₂ hK₂ h₂]
  exact propext AddRightCancel.add_right_cancel_iff

theorem le_cancel_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [IsPreorder α] [OrderedRing α]
    (ctx : Context α) (K : Nat) (a b a' b' c : Expr)
    (hl₁ : Expr.linSOk_k a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronLinEval_k K = (a'.add c).kronLinEval_k K)
    (hl₂ : Expr.linSOk_k b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronLinEval_k K = (b'.add c).kronLinEval_k K) :
    (a.denoteS ctx ≤ b.denoteS ctx) = (a'.denoteS ctx ≤ b'.denoteS ctx) := by
  rw [Expr.eq_of_kronLinS ctx K a (a'.add c) hl₁ hK₁ h₁, Expr.eq_of_kronLinS ctx K b (b'.add c) hl₂ hK₂ h₂]
  exact propext (OrderedAdd.add_le_left_iff _).symm

theorem lt_cancel_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    [OrderedRing α] (ctx : Context α) (K : Nat) (a b a' b' c : Expr)
    (hl₁ : Expr.linSOk_k a (a'.add c) = true) (hK₁ : Expr.kronOk_k K a (a'.add c) = true)
    (h₁ : a.kronLinEval_k K = (a'.add c).kronLinEval_k K)
    (hl₂ : Expr.linSOk_k b (b'.add c) = true) (hK₂ : Expr.kronOk_k K b (b'.add c) = true)
    (h₂ : b.kronLinEval_k K = (b'.add c).kronLinEval_k K) :
    (a.denoteS ctx < b.denoteS ctx) = (a'.denoteS ctx < b'.denoteS ctx) := by
  rw [Expr.eq_of_kronLinS ctx K a (a'.add c) hl₁ hK₁ h₁, Expr.eq_of_kronLinS ctx K b (b'.add c) hl₂ hK₂ h₂]
  exact propext (OrderedAdd.add_lt_left_iff _).symm

end Lean.Grind.CommRing
