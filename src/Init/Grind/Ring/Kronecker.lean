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

end Lean.Grind.CommRing
