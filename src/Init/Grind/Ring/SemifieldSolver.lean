/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Grind.Ring.FieldSolver
public import Init.Grind.Ring.CommSemiringAdapter
import Init.Data.Int.DivMod.Lemmas
import Init.Omega

/-!
# Rational coefficients over semifields

The numerator and denominator computation in `FieldSolver` also works for semirings.
These certificates interpret its numerator using nonnegative coefficients and require
no additive cancellation.
-/

@[expose] public section
namespace Lean.Grind.CommRing
attribute [local instance] Semiring.natCast

theorem Poly.cancelVar'_nonneg (p : Poly) (c : Int) (x : Var) (acc : Poly)
    (hc : 0 ≤ c) (hp : p.NonnegCoeffs) (ha : acc.NonnegCoeffs) :
    (p.cancelVar' c x acc).NonnegCoeffs := by
  induction p generalizing acc with
  | num k =>
    cases hp with
    | num _ hk => exact Poly.addConst_NonnegCoeffs hk ha
  | add k m p ih =>
    cases hp with
    | add _ _ _ hk hp =>
      simp only [Poly.cancelVar', cond_eq_ite]
      split
      · exact ih _ hp (Poly.insert_Nonneg _ _ _ (Int.ediv_nonneg hk (Int.pow_nonneg hc)) ha)
      · exact ih _ hp (Poly.insert_Nonneg _ _ _ hk ha)

theorem Poly.denoteS_cancelVar' [CommSemiring α] (ctx : Context α) (p : Poly)
    (c : Int) (x : Var) (acc : Poly) (hc : 0 < c)
    (hp : p.NonnegCoeffs) (ha : acc.NonnegCoeffs)
    (hx : (c.toNat : α) * x.denote ctx = 1) :
    (p.cancelVar' c x acc).denoteS ctx = p.denoteS ctx + acc.denoteS ctx := by
  induction p generalizing acc with
  | num k =>
    cases hp with
    | num _ hk =>
      simpa [Poly.cancelVar', Poly.denoteS, denoteSInt_eq, Semiring.add_comm]
        using Poly.denoteS_addConst ctx acc k hk ha
  | add k m p ih =>
    cases hp with
    | add _ _ _ hk hp =>
      simp only [Poly.cancelVar', cond_eq_ite]
      split
      · rename_i h
        have hc' : 0 ≤ c := Int.le_of_lt hc
        have hq : 0 ≤ k / c ^ m.degreeOf x := Int.ediv_nonneg hk (Int.pow_nonneg hc')
        rw [ih _ hp (Poly.insert_Nonneg _ _ _ hq ha), Poly.denoteS_insert ctx _ _ _ hq ha]
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        have hd : c ^ m.degreeOf x ∣ k := h.2
        have hnat : k.toNat = (k / c ^ m.degreeOf x).toNat * c.toNat ^ m.degreeOf x := by
          conv => lhs; rw [← Int.ediv_mul_cancel hd]
          rw [Int.toNat_mul hq (Int.pow_nonneg hc'), Int.toNat_pow_of_nonneg hc']
        rw [Poly.denoteS, denoteSInt_eq, Mon.denote_cancelVar ctx m x, hnat,
          Semiring.natCast_mul, Semiring.natCast_pow]
        have hpow := congrArg (fun a : α => a ^ m.degreeOf x) hx
        rw [CommSemiring.mul_pow, Semiring.one_pow] at hpow
        simp only [Semiring.mul_assoc, ← Semiring.add_assoc]
        rw [← Semiring.mul_assoc ((c.toNat : α) ^ m.degreeOf x)]
        rw [hpow, Semiring.one_mul]
        simp [Semiring.add_assoc, Semiring.add_comm]
      · rw [ih _ hp (Poly.insert_Nonneg _ _ _ hk ha), Poly.denoteS_insert ctx _ _ _ hk ha]
        simp [Poly.denoteS, denoteSInt_eq, Semiring.add_assoc,
          AddCommMonoid.add_left_comm]

theorem Poly.denoteS_cancelVar [CommSemiring α] (ctx : Context α) (p : Poly)
    (c : Int) (x : Var) (hc : 0 < c) (hp : p.NonnegCoeffs)
    (hx : (c.toNat : α) * x.denote ctx = 1) :
    (p.cancelVar c x).denoteS ctx = p.denoteS ctx := by
  simpa [Poly.cancelVar, Poly.denoteS, denoteSInt_eq, Semiring.natCast_zero, Semiring.add_zero]
    using Poly.denoteS_cancelVar' ctx p c x (.num 0) hc hp Poly.num_zero_NonnegCoeffs hx

theorem Poly.cancelVar_nonneg (p : Poly) (c : Int) (x : Var)
    (hc : 0 ≤ c) (hp : p.NonnegCoeffs) : (p.cancelVar c x).NonnegCoeffs :=
  p.cancelVar'_nonneg c x (.num 0) hc hp Poly.num_zero_NonnegCoeffs

theorem Poly.divConst_nonneg (p : Poly) (c : Int)
    (hc : 0 ≤ c) (hp : p.NonnegCoeffs) : (p.divConst c).NonnegCoeffs := by
  induction p with
  | num k => cases hp with
    | num _ hk => exact .num _ (Int.ediv_nonneg hk hc)
  | add k m p ih => cases hp with
    | add _ _ _ hk hp => exact .add _ _ _ (Int.ediv_nonneg hk hc) (ih hp)

def PolyQ.denoteS [Semifield α] (ctx : Context α) (q : PolyQ) : α :=
  q.num.denoteS ctx * (q.den : α)⁻¹

theorem Poly.substInv_nonneg (p : Poly) (x : Var) (c : Nat)
    (hp : p.NonnegCoeffs) : (p.substInv x c).num.NonnegCoeffs := by
  simp only [Poly.substInv, cond_eq_ite]
  split
  · exact hp
  · exact Poly.cancelVar_nonneg _ _ _ (Int.natCast_nonneg _)
      (Poly.mulConst_NonnegCoeffs (Int.natCast_nonneg _) hp)

theorem Poly.denoteS_substInv [Semifield α] [IsCharP α 0] (ctx : Context α)
    (p : Poly) (x : Var) (c : Nat) (hp : p.NonnegCoeffs)
    (hx : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) :
    (p.substInv x c).denoteS ctx = p.denoteS ctx := by
  simp only [Poly.substInv, PolyQ.denoteS, cond_eq_ite]
  split
  · rename_i hc
    simp only [beq_iff_eq] at hc
    subst c
    simp [Semiring.natCast_one, Semifield.inv_one, Semiring.mul_one]
  · rename_i hc
    simp only [beq_iff_eq] at hc
    have hc' : (c : α) ≠ 0 := Semifield.natCast_ne_zero hc
    have h1 : ((c : Int).toNat : α) * x.denote ctx = 1 := by
      rw [Int.toNat_natCast, hx, Semiring.ofNat_eq_natCast]
      exact Semifield.mul_inv_cancel hc'
    have hpow : (c : α)^p.maxDegreeOf x ≠ 0 := fun h => hc' (Semifield.of_pow_eq_zero _ _ h)
    rw [Poly.denoteS_cancelVar ctx _ (c : Int) x (by omega)
        (Poly.mulConst_NonnegCoeffs (Int.natCast_nonneg _) hp) h1,
      Poly.denoteS_mulConst ctx _ p (Int.natCast_nonneg _) hp,
      Int.toNat_natCast, Semiring.natCast_pow]
    rw [CommSemiring.mul_comm _ (p.denoteS ctx), Semiring.mul_assoc,
      Semifield.mul_inv_cancel hpow, Semiring.mul_one]

theorem PolyQ.denoteS_substInv [Semifield α] [IsCharP α 0] (ctx : Context α)
    (q : PolyQ) (x : Var) (c : Nat) (hq : q.num.NonnegCoeffs)
    (hx : x.denote ctx = (OfNat.ofNat (α := α) c)⁻¹) :
    (q.substInv x c).denoteS ctx = q.denoteS ctx := by
  have h := Poly.denoteS_substInv ctx q.num x c hq hx
  simp only [PolyQ.substInv, PolyQ.denoteS] at h ⊢
  rw [Semiring.natCast_mul, Semifield.inv_mul, ← h, Semiring.mul_assoc,
    CommSemiring.mul_comm ((q.den : α)⁻¹)]

theorem PolyQ.denoteS_reduce [Semifield α] [IsCharP α 0] (ctx : Context α)
    (q : PolyQ) (hq : q.num.NonnegCoeffs) : q.reduce.denoteS ctx = q.denoteS ctx := by
  unfold PolyQ.reduce
  simp only [cond_eq_ite]
  split
  · rfl
  · rename_i hg
    split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      simp only [decide_eq_true_eq, Nat.not_le] at hg
      generalize Nat.gcd q.num.gcdCoeffs q.den = g at *
      have hg' : (g : α) ≠ 0 := Semifield.natCast_ne_zero (by omega)
      have hn := q.num.divConst_nonneg (g : Int) (Int.natCast_nonneg _) hq
      generalize q.num.divConst (g : Int) = num at *
      generalize q.den / g = den at *
      simp only [PolyQ.denoteS]
      rw [← h.1, ← h.2,
        Poly.denoteS_mulConst ctx _ _ (Int.natCast_nonneg _) hn,
        Int.toNat_natCast, Semiring.natCast_mul, Semifield.mul_mul_inv_cancel hg']
    · rfl

theorem Poly.denoteS_toPolyQ [Semifield α] [IsCharP α 0] (ctx : Context α)
    (p : Poly) (invs : InvVars) (hp : p.NonnegCoeffs) (h : invs.ok ctx) :
    (p.toPolyQ invs []).denoteS ctx = p.denoteS ctx := by
  let q := invs.foldl (fun q xc => q.substInv xc.1 xc.2) (PolyQ.mk p 1)
  have go : ∀ (invs : InvVars) (q : PolyQ), q.num.NonnegCoeffs → invs.ok ctx →
      (invs.foldl (fun q xc => q.substInv xc.1 xc.2) q).denoteS ctx = q.denoteS ctx ∧
      (invs.foldl (fun q xc => q.substInv xc.1 xc.2) q).num.NonnegCoeffs := by
    intro invs
    induction invs with
    | nil => intro q hq _; exact ⟨rfl, hq⟩
    | cons xc invs ih =>
      intro q hq hok
      rw [InvVars.ok_cons] at hok
      obtain ⟨hd, hn⟩ := ih (q.substInv xc.1 xc.2) (q.num.substInv_nonneg _ _ hq) hok.2
      exact ⟨hd.trans (PolyQ.denoteS_substInv ctx q xc.1 xc.2 hq hok.1), hn⟩
  obtain ⟨hd, hn⟩ := go invs (PolyQ.mk p 1) hp h
  change q.reduce.denoteS ctx = p.denoteS ctx
  rw [PolyQ.denoteS_reduce ctx q hn, hd]
  simp [PolyQ.denoteS, Semiring.natCast_one, Semifield.inv_one, Semiring.mul_one]

/-- Normalize a semiring expression, treating the recorded numeral inverses as coefficients. -/
def Expr.toPolyQS (e : Expr) (invs : InvVars) : PolyQ := e.toPolyS.toPolyQ invs []

theorem Expr.eq_of_toPolyQS_eq [Semifield α] [IsCharP α 0] (ctx : Context α)
    (invs : InvVars) (hok : invs.ok ctx) (a b : Expr)
    (h : a.toPolyQS invs == b.toPolyQS invs) : a.denoteS ctx = b.denoteS ctx := by
  have h := congrArg (PolyQ.denoteS ctx) (eq_of_beq h)
  rw [Expr.toPolyQS, Expr.toPolyQS,
    Poly.denoteS_toPolyQ ctx a.toPolyS invs Expr.toPolyS_NonnegCoeffs hok,
    Poly.denoteS_toPolyQ ctx b.toPolyS invs Expr.toPolyS_NonnegCoeffs hok,
    Expr.denoteS_toPolyS, Expr.denoteS_toPolyS] at h
  exact h

end Lean.Grind.CommRing
