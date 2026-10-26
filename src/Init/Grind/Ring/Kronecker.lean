/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Packed
import Init.Omega
import Init.ByCases
import Init.Data.Int.Order
import Init.Data.Int.LemmasAux
import Init.Data.Nat.Lemmas

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
    (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : degOk_k B a b = true) (hK : kronOk_k K a b = true)
    (h : a.kronEval_k K B = b.kronEval_k K B) : a.denoteS ctx = b.denoteS ctx := by
  have hS := semi_k_and hS
  apply Ring.OfSemiring.toQ_inj
  rw [← Expr.denoteAsRing_eq, ← Expr.denoteAsRing_eq, ← denote_mapCtx_toQ ctx a hS.1, ← denote_mapCtx_toQ ctx b hS.2]
  exact Expr.eq_of_kron _ K B a b hB hK h

theorem eq_true_of_kronS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K B : Nat) (a b : Expr)
    (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : Expr.degOk_k B a b = true) (hK : Expr.kronOk_k K a b = true)
    (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx = b.denoteS ctx) = True :=
  eq_true (Expr.eq_of_kronS ctx K B a b hS hB hK h)

theorem le_true_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [IsPreorder α] (ctx : Context α) (K B : Nat)
    (a b : Expr) (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : Expr.degOk_k B a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx ≤ b.denoteS ctx) = True := by
  rw [Expr.eq_of_kronS ctx K B a b hS hB hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kronS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    (ctx : Context α) (K B : Nat) (a b : Expr) (hS : Bool.rec false b.semi_k a.semi_k = true) (hB : Expr.degOk_k B a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronEval_k K B = b.kronEval_k K B) : (a.denoteS ctx < b.denoteS ctx) = False := by
  rw [Expr.eq_of_kronS ctx K B a b hS hB hK h]; exact eq_false Std.lt_irrefl

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

/-- Checks that `a` and `b` are linear (`Expr.degB_k ≤ 1`). -/
noncomputable def Expr.linOk_k (a b : Expr) : Bool :=
  Bool.rec false (Nat.ble b.degB_k 1) (Nat.ble a.degB_k 1)

theorem Expr.eq_of_kronLin {α} [CommRing α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hl : linOk_k a b = true) (hK : kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) :
    a.denote ctx = b.denote ctx := by
  have hl := PPoly.and_of_rec hl
  have ha := Nat.le_of_ble_eq_true hl.1
  have hb := Nat.le_of_ble_eq_true hl.2
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

theorem Expr.eq_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hS : Bool.rec false b.semi_k a.semi_k = true) (hl : linOk_k a b = true) (hK : kronOk_k K a b = true)
    (h : a.kronLinEval_k K = b.kronLinEval_k K) : a.denoteS ctx = b.denoteS ctx := by
  have hS := semi_k_and hS
  apply Ring.OfSemiring.toQ_inj
  rw [← Expr.denoteAsRing_eq, ← Expr.denoteAsRing_eq, ← denote_mapCtx_toQ ctx a hS.1, ← denote_mapCtx_toQ ctx b hS.2]
  exact Expr.eq_of_kronLin _ K a b hl hK h

theorem eq_true_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] (ctx : Context α) (K : Nat) (a b : Expr)
    (hS : Bool.rec false b.semi_k a.semi_k = true) (hl : Expr.linOk_k a b = true) (hK : Expr.kronOk_k K a b = true)
    (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx = b.denoteS ctx) = True :=
  eq_true (Expr.eq_of_kronLinS ctx K a b hS hl hK h)

theorem le_true_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [IsPreorder α] (ctx : Context α) (K : Nat)
    (a b : Expr) (hS : Bool.rec false b.semi_k a.semi_k = true) (hl : Expr.linOk_k a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx ≤ b.denoteS ctx) = True := by
  rw [Expr.eq_of_kronLinS ctx K a b hS hl hK h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_kronLinS {α} [CommSemiring α] [AddRightCancel α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α]
    (ctx : Context α) (K : Nat) (a b : Expr) (hS : Bool.rec false b.semi_k a.semi_k = true) (hl : Expr.linOk_k a b = true)
    (hK : Expr.kronOk_k K a b = true) (h : a.kronLinEval_k K = b.kronLinEval_k K) : (a.denoteS ctx < b.denoteS ctx) = False := by
  rw [Expr.eq_of_kronLinS ctx K a b hS hl hK h]; exact eq_false Std.lt_irrefl

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
theorem KList.denote_eq {α} [CommRing α] (ctx : Context α) (K B c : Nat) (p₁ p E : Poly) (ls : KList)
    (hB : 1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ E.maxDeg_k < B ∧ ls.ok_k B = true)
    (hK : 2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K)
    (h : p.kron_k K B = p₁.kron_k K B + ls.kron_k K B + c * E.kron_k K B) (hz : ls.AllZero ctx) :
    p.denote ctx = p₁.denote ctx + (c : α) * E.denote ctx := by
  obtain ⟨hB, hp, hp₁, hE, hok⟩ := hB
  have hl := KList.toPP_spec ctx K B hB ls hok
  have sp := Poly.toPP_k_spec ctx hB p hp
  have sp₁ := Poly.toPP_k_spec ctx hB p₁ hp₁
  have sE := Poly.toPP_k_spec ctx hB E hE
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have hEc := PPoly.mulConst_k_spec (Var.denote ctx) B (B - 1) (c : Int) (E.toPP_k B)
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (p.toPP_k B)
    ((p₁.toPP_k B).append ((ls.toPP B).append ((E.toPP_k B).mulConst_k (c : Int))))
    (by
      rw [PPoly.kron_append, PPoly.kron_append, PPoly.kron_mulConst_k, ← Poly.kron_k_eq, ← Poly.kron_k_eq,
        ← Poly.kron_k_eq, hl.1, h, Int.add_assoc])
    (by
      have h₁ := PPoly.norm1_append (p₁.toPP_k B) ((ls.toPP B).append ((E.toPP_k B).mulConst_k (c : Int)))
      have h₂ := PPoly.norm1_append (ls.toPP B) ((E.toPP_k B).mulConst_k (c : Int))
      have h₃ := PPoly.norm1_mulConst_k (c : Int) (E.toPP_k B)
      rw [← Poly.norm1_k_eq] at h₁ h₃
      have h₄ := hl.2.1
      rw [show ((c : Int)).natAbs = c from rfl] at h₃
      have : 2 * ((p.toPP_k B).norm1 + ((p₁.toPP_k B).append ((ls.toPP B).append ((E.toPP_k B).mulConst_k (c : Int)))).norm1) < 2 ^ K := by
        rw [← Poly.norm1_k_eq]
        have := Nat.mul_le_mul_left c (Nat.le_refl E.norm1_k)
        omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [PPoly.denote_append, PPoly.denote_append, hEc.1, sp.1, sp₁.1, sE.1, hl.2.2 hz, zero_add] at heq
  rw [heq]; congr 1; rw [intCast_natCast]

/-- `e` and `p + c * E` have the same value at the point, so they denote the same. -/
theorem Expr.denote_eq_of_kron_poly {α} [CommRing α] (ctx : Context α) (K B c : Nat) (e : Expr) (p E : Poly)
    (hB : 1 < B ∧ e.degB_k < B ∧ p.maxDeg_k < B ∧ E.maxDeg_k < B)
    (hK : 2 * (e.majorant_k + p.norm1_k + c * E.norm1_k) < 2 ^ K)
    (h : e.kronEval_k K B = p.kron_k K B + c * E.kron_k K B) :
    e.denote ctx = p.denote ctx + (c : α) * E.denote ctx := by
  obtain ⟨hB, he, hp, hE⟩ := hB
  have sp := Poly.toPP_k_spec ctx hB p hp
  have sE := Poly.toPP_k_spec ctx hB E hE
  have hX : (0 : Int) < 2 ^ K := Int.pow_pos (by decide)
  have hEc := PPoly.mulConst_k_spec (Var.denote ctx) B (B - 1) (c : Int) (E.toPP_k B)
  have heq := PPoly.denote_eq_of_kron (Var.denote ctx) B ((2 : Int) ^ K) hX (e.toPP_k B)
    ((p.toPP_k B).append ((E.toPP_k B).mulConst_k (c : Int)))
    (by
      rw [PPoly.kron_append, PPoly.kron_mulConst_k, ← Poly.kron_k_eq, ← Poly.kron_k_eq, ← PPoly.denote_kron _ hB,
        denote_toPP_k _ B hB e he, ← kronEval_k_eq, h])
    (by
      have h₁ := PPoly.norm1_append (p.toPP_k B) ((E.toPP_k B).mulConst_k (c : Int))
      have h₃ := PPoly.norm1_mulConst_k (c : Int) (E.toPP_k B)
      rw [← Poly.norm1_k_eq] at h₁ h₃
      rw [show ((c : Int)).natAbs = c from rfl] at h₃
      have h₄ := norm1_toPPAcc_k B e (.num (Int.ofNat 0))
      rw [show (PPoly.num (Int.ofNat 0)).norm1 = 0 from rfl, Nat.add_zero] at h₄
      have : 2 * ((e.toPP_k B).norm1 + ((p.toPP_k B).append ((E.toPP_k B).mulConst_k (c : Int))).norm1) < 2 ^ K := by
        have := Nat.mul_le_mul_left c (Nat.le_refl E.norm1_k)
        unfold toPP_k; omega
      have h2 : ((2 ^ K : Nat) : Int) = (2 : Int) ^ K := Int.natCast_pow 2 K
      rw [← h2]; exact Int.ofNat_lt.mpr (by simpa using this))
  rw [PPoly.denote_append, hEc.1, sp.1, sE.1, denote_toPP_k _ B hB e he] at heq
  rw [Expr.denote_eq_denoteF, heq]; congr 1; rw [intCast_natCast]

namespace Stepwise

/-- The checks of the Kronecker certificates of `grind`'s steps: degrees below `B`, coefficients below `2 ^ K`. -/
noncomputable def kronOk_k (K B c : Nat) (p₁ p E : Poly) (ls : KList) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.blt (Nat.mul 2 (Nat.add (Nat.add (Nat.add p.norm1_k p₁.norm1_k) ls.norm_k) (Nat.mul c E.norm1_k))) (Nat.pow 2 K))
    (ls.ok_k B)) (Nat.blt E.maxDeg_k B)) (Nat.blt p₁.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt 1 B)

theorem of_kronOk_k {K B c : Nat} {p₁ p E : Poly} {ls : KList} (h : kronOk_k K B c p₁ p E ls = true) :
    (1 < B ∧ p.maxDeg_k < B ∧ p₁.maxDeg_k < B ∧ E.maxDeg_k < B ∧ ls.ok_k B = true) ∧
    2 * (p.norm1_k + p₁.norm1_k + ls.norm_k + c * E.norm1_k) < 2 ^ K := by
  unfold kronOk_k at h
  have h₁ := PPoly.and_of_rec h
  have h₂ := PPoly.and_of_rec h₁.2
  have h₃ := PPoly.and_of_rec h₂.2
  have h₄ := PPoly.and_of_rec h₃.2
  have h₅ := PPoly.and_of_rec h₄.2
  exact ⟨⟨Nat.blt_eq.mp h₁.1, Nat.blt_eq.mp h₂.1, Nat.blt_eq.mp h₃.1, Nat.blt_eq.mp h₄.1, h₅.1⟩, Nat.blt_eq.mp h₅.2⟩

theorem simpsK {α} [CommRing α] (ctx : Context α) (K B : Nat) (p₁ p : Poly) (ls : KList)
    (hB : kronOk_k K B 0 p₁ p (.num 0) ls = true) (h : Int.beq' (p.kron_k K B) (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) = true) :
    ls.AllZero ctx → p₁.denote ctx = 0 → p.denote ctx = 0 := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B 0 p₁ p (.num 0) ls hB.1 hB.2 (by rw [h, Int.add_k_eq]; simp) hz, h₁]
  simp [Semiring.natCast_zero, zero_mul, add_zero]

theorem simpsKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (p₁ p E : Poly) (ls : KList)
    (hB : kronOk_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K B))) = true) :
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

theorem d_stepsKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (k : Int) (init : Poly) (K B : Nat) (p₁ p E : Poly) (ls : KList)
    (hB : kronOk_k K B c p₁ p E ls = true)
    (h : Int.beq' (p.kron_k K B) (Int.add_k (Int.add_k (p₁.kron_k K B) (ls.kron_k K B)) (Int.mul_k (Int.ofNat c) (E.kron_k K B))) = true) :
    ls.AllZero ctx → k * init.denote ctx = p₁.denote ctx → k * init.denote ctx = p.denote ctx := by
  intro hz h₁
  have hB := of_kronOk_k hB
  rw [Int.beq'_eq] at h
  rw [KList.denote_eq ctx K B c p₁ p E ls hB.1 hB.2 (by rw [h, Int.add_k_eq, Int.add_k_eq, Int.mul_k_eq]; rfl) hz, h₁,
    (IsCharP.natCast_eq_zero_iff c c).mpr (Nat.mod_self c), zero_mul, add_zero]

/-- The checks of the Kronecker certificates of `grind`'s implications. -/
noncomputable def impOk_k (K B c : Nat) (e : Expr) (p E : Poly) : Bool :=
  Bool.rec false (Bool.rec false (Bool.rec false (Bool.rec false
    (Nat.blt (Nat.mul 2 (Nat.add (Nat.add e.majorant_k p.norm1_k) (Nat.mul c E.norm1_k))) (Nat.pow 2 K))
    (Nat.blt E.maxDeg_k B)) (Nat.blt p.maxDeg_k B)) (Nat.blt e.degB_k B)) (Nat.blt 1 B)

theorem of_impOk_k {K B c : Nat} {e : Expr} {p E : Poly} (h : impOk_k K B c e p E = true) :
    (1 < B ∧ e.degB_k < B ∧ p.maxDeg_k < B ∧ E.maxDeg_k < B) ∧ 2 * (e.majorant_k + p.norm1_k + c * E.norm1_k) < 2 ^ K := by
  unfold impOk_k at h
  have h₁ := PPoly.and_of_rec h
  have h₂ := PPoly.and_of_rec h₁.2
  have h₃ := PPoly.and_of_rec h₂.2
  have h₄ := PPoly.and_of_rec h₃.2
  exact ⟨⟨Nat.blt_eq.mp h₁.1, Nat.blt_eq.mp h₂.1, Nat.blt_eq.mp h₃.1, Nat.blt_eq.mp h₄.1⟩, Nat.blt_eq.mp h₄.2⟩

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

theorem imp_1eqKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) (K B : Nat) (lhs rhs : Expr) (p₁ p₂ E : Poly)
    (hB : impOk_k K B c (lhs.sub rhs) p₁ E = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (Int.add_k (p₁.kron_k K B) (Int.mul_k (Int.ofNat c) (E.kron_k K B))) = true)
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
  rw [this, h₁]; simp [Poly.denote, Semiring.natCast_zero, zero_mul, add_zero]

theorem imp_keqKC {α c} [CommRing α] [IsCharP α c] (ctx : Context α) [NoNatZeroDivisors α] (k : Int) (K B : Nat) (lhs rhs : Expr)
    (p₁ p₂ E : Poly) (hk : Int.beq' k 0 = false) (hB : impOk_k K B c (lhs.sub rhs) p₁ E = true)
    (h : Int.beq' ((lhs.sub rhs).kronEval_k K B) (Int.add_k (p₁.kron_k K B) (Int.mul_k (Int.ofNat c) (E.kron_k K B))) = true)
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

end Lean.Grind.CommRing
