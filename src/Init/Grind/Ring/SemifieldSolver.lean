/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Grind.Ring.FieldSolver
public import Init.Grind.Ring.Kronecker
public import Init.Grind.Ring.CommSemiringAdapter
import Init.Data.Int.DivMod.Lemmas
import Init.Omega
import Init.ByCases
import Init.Data.Nat.Lemmas

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
noncomputable def Expr.toPolyQS_cert (bal : Bool) (invs : InvVars) (a b : Expr) : Bool :=
  ((a.toPolySX_k bal).toPolyQ_k invs []).beq' ((b.toPolySX_k bal).toPolyQ_k invs [])

theorem Expr.eq_of_toPolyQS_eq [Semifield α] [IsCharP α 0] (ctx : Context α) (bal : Bool)
    (invs : InvVars) (hok : invs.ok ctx) (a b : Expr)
    (h : toPolyQS_cert bal invs a b) : a.denoteS ctx = b.denoteS ctx := by
  simp only [toPolyQS_cert, PolyQ.beq'_eq, Poly.toPolyQ_k_eq_toPolyQ] at h
  have ha := Expr.toPolySX_k_nonneg ctx bal a
  have hb := Expr.toPolySX_k_nonneg ctx bal b
  have h := congrArg (PolyQ.denoteS ctx) h
  rw [Poly.denoteS_toPolyQ ctx _ invs ha.1 hok,
    Poly.denoteS_toPolyQ ctx _ invs hb.1 hok, ha.2, hb.2] at h
  exact h

/-- Look up an inverse variable in the sorted certificate list. -/
def InvVars.lookupSorted (invs : InvVars) (x : Var) : Option Nat :=
  match invs with
  | [] => none
  | (y, c) :: invs => if x < y then none else if y == x then some c else lookupSorted invs x

theorem InvVars.lookupSorted_eq (invs : InvVars) (x : Var) :
    InvVars.lookupSorted invs x = invs.lookup_k x := by
  induction invs with
  | nil => rfl
  | cons p invs ih =>
    change (if x < p.1 then none else if p.1 == x then some p.2 else InvVars.lookupSorted invs x) =
      Bool.rec (Bool.rec (InvVars.lookup_k invs x) (some p.2) (Nat.beq p.1 x)) none (Nat.blt x p.1)
    rw [← ih]
    by_cases h : x < p.1
    · simp only [h, ite_true, Nat.blt_eq.mpr h]
    · have hb : Nat.blt x p.1 = false := Bool.eq_false_iff.mpr (fun hb => h (Nat.blt_eq.mp hb))
      simp only [h, ite_false, hb]
      change (if Nat.beq p.1 x then some p.2 else InvVars.lookupSorted invs x) =
        Bool.rec (InvVars.lookupSorted invs x) (some p.2) (Nat.beq p.1 x)
      cases Nat.beq p.1 x <;> rfl

/-- Clear inverse numerals without expanding polynomial products. -/
def Expr.clearDenoms (invs : InvVars) : Expr → Expr × Nat
  | .num k => (.num k, 1)
  | .natCast n => (.natCast n, 1)
  | .intCast _ | .neg _ | .sub _ _ => (.num 0, 1)
  | .var x => match InvVars.lookupSorted invs x with
    | some c => (.num 1, c)
    | none => (.var x, 1)
  | .add a b =>
    let (a, da) := a.clearDenoms invs
    let (b, db) := b.clearDenoms invs
    (.add (.mul a (.num db)) (.mul b (.num da)), da * db)
  | .mul a b =>
    let (a, da) := a.clearDenoms invs
    let (b, db) := b.clearDenoms invs
    (.mul a b, da * db)
  | .pow a n =>
    let (a, d) := a.clearDenoms invs
    (.pow a n, d ^ n)

noncomputable def Expr.clearDenoms_k (invs : InvVars) (e : Expr) : Expr × Nat :=
  Expr.rec
    (fun k => (.num k, 1)) (fun n => (.natCast n, 1)) (fun _ => (.num 0, 1))
    (fun x => Option.rec (.var x, 1) (fun c => (.num 1, c)) (invs.lookup_k x))
    (fun _ _ => (.num 0, 1))
    (fun _ _ a b => (.add (.mul a.1 (.num b.2)) (.mul b.1 (.num a.2)), Nat.mul a.2 b.2))
    (fun _ _ _ _ => (.num 0, 1))
    (fun _ _ a b => (.mul a.1 b.1, Nat.mul a.2 b.2))
    (fun _ n a => (.pow a.1 n, Nat.pow a.2 n)) e

theorem Expr.clearDenoms_k_eq (invs : InvVars) (e : Expr) :
    e.clearDenoms_k invs = e.clearDenoms invs := by
  induction e with
  | var x =>
    simp only [clearDenoms_k, clearDenoms, InvVars.lookupSorted_eq]
    cases invs.lookup_k x <;> rfl
  | _ => simp_all [clearDenoms_k, clearDenoms, Nat.pow_eq]

theorem Expr.clearDenoms_spec {α} [Semifield α] [IsCharP α 0] (ctx : Context α)
    (invs : InvVars) (hok : invs.ok ctx) (hnz : invs.nonzero_k = true) (e : Expr) :
    (e.clearDenoms invs).1.denoteS ctx = ((e.clearDenoms invs).2 : α) * e.denoteS ctx ∧
    (e.clearDenoms invs).2 ≠ 0 := by
  induction e with
  | num k => exact ⟨by simp [clearDenoms, Semiring.natCast_one, Semiring.one_mul], Nat.one_ne_zero⟩
  | natCast n => exact ⟨by simp [clearDenoms, Semiring.natCast_one, Semiring.one_mul], Nat.one_ne_zero⟩
  | intCast k | neg a _ | sub a b _ _ =>
    refine ⟨?_, Nat.one_ne_zero⟩
    change OfNat.ofNat (α := α) 0 = (NatCast.natCast 1 : α) * 0
    rw [Semiring.ofNat_eq_natCast, Semiring.natCast_zero, Semiring.mul_zero]
  | var x =>
    cases h : InvVars.lookupSorted invs x with
    | none => exact ⟨by simp [clearDenoms, h, Semiring.natCast_one, Semiring.one_mul], by simp [clearDenoms, h]⟩
    | some c =>
      have hc := InvVars.lookup_k_spec ctx invs hok hnz x c (by rwa [← InvVars.lookupSorted_eq])
      refine ⟨?_, by simpa [clearDenoms, h] using hc.2⟩
      simp only [clearDenoms, h, Expr.denoteS_num, Int.natAbs_one, Expr.denoteS_var]
      rw [hc.1, Semifield.mul_inv_cancel (Semifield.natCast_ne_zero hc.2)]
  | add a b iha ihb =>
    refine ⟨?_, Nat.mul_ne_zero iha.2 ihb.2⟩
    simp only [clearDenoms, Expr.denoteS_add, Expr.denoteS_mul, Expr.denoteS_num,
      Int.natAbs_natCast, Semiring.ofNat_eq_natCast, iha.1, ihb.1, Semiring.natCast_mul,
      Semiring.left_distrib]
    simp only [Semiring.mul_assoc, CommSemiring.mul_left_comm, CommSemiring.mul_comm]
  | mul a b iha ihb =>
    refine ⟨?_, Nat.mul_ne_zero iha.2 ihb.2⟩
    simp only [clearDenoms, Expr.denoteS_mul, iha.1, ihb.1, Semiring.natCast_mul]
    simp only [Semiring.mul_assoc, CommSemiring.mul_left_comm]
  | pow a n ih =>
    refine ⟨?_, Nat.ne_of_gt (Nat.pow_pos (Nat.pos_of_ne_zero ih.2))⟩
    simp only [clearDenoms, Expr.denoteS_pow, ih.1, CommSemiring.mul_pow, Semiring.natCast_pow]

theorem Expr.eq_of_clearDenoms {α} [Semifield α] [IsCharP α 0] (ctx : Context α)
    (invs : InvVars) (hok : invs.ok ctx) (hnz : invs.nonzero_k = true) (a b a' b' : Expr) (da db : Nat)
    (ha : a.clearDenoms_k invs = (a', da)) (hb : b.clearDenoms_k invs = (b', db))
    (h : (a'.mul (.num db)).denoteS ctx = (b'.mul (.num da)).denoteS ctx) :
    a.denoteS ctx = b.denoteS ctx := by
  have ha' := a.clearDenoms_spec ctx invs hok hnz
  have hb' := b.clearDenoms_spec ctx invs hok hnz
  rw [clearDenoms_k_eq] at ha hb
  rw [ha] at ha'
  rw [hb] at hb'
  simp only [Expr.denoteS_mul, Expr.denoteS_num, Int.natAbs_natCast, Semiring.ofNat_eq_natCast] at h
  rw [ha'.1, hb'.1] at h
  have hd : ((da * db : Nat) : α) ≠ 0 := Semifield.natCast_ne_zero (Nat.mul_ne_zero ha'.2 hb'.2)
  have h' : ((da * db : Nat) : α) * a.denoteS ctx = ((da * db : Nat) : α) * b.denoteS ctx := by
    simpa only [Semiring.natCast_mul, Semiring.mul_assoc, CommSemiring.mul_left_comm, CommSemiring.mul_comm] using h
  have h' := congrArg (fun x : α => ((da * db : Nat) : α)⁻¹ * x) h'
  simpa only [← Semiring.mul_assoc, Semifield.inv_mul_cancel hd, Semiring.one_mul] using h'

end Lean.Grind.CommRing
