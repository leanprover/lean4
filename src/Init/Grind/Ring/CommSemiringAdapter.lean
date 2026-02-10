/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.Envelope
public import Init.Grind.Ring.CommSolver
import Init.Data.Int.LemmasAux
import Init.Omega
@[expose] public section
namespace Lean.Grind
namespace CommRing

def Expr.denoteS {α} [Semiring α] (ctx : Context α) : Expr → α
  | .num k     => OfNat.ofNat (α := α) k.natAbs
  | .natCast k => OfNat.ofNat (α := α) k
  | .var v     => v.denote ctx
  | .add a b   => denoteS ctx a + denoteS ctx b
  | .mul a b   => denoteS ctx a * denoteS ctx b
  | .pow a k   => denoteS ctx a ^ k
  | .sub .. | .neg .. | .intCast .. => 0

def Expr.denoteSAsRing {α} [Semiring α] (ctx : Context α) : Expr → Ring.OfSemiring.Q α
  | .num k     => OfNat.ofNat (α := Ring.OfSemiring.Q α) k.natAbs
  | .natCast k => OfNat.ofNat (α := Ring.OfSemiring.Q α) k
  | .var v     => Ring.OfSemiring.toQ (v.denote ctx)
  | .add a b   => denoteSAsRing ctx a + denoteSAsRing ctx b
  | .mul a b   => denoteSAsRing ctx a * denoteSAsRing ctx b
  | .pow a k   => denoteSAsRing ctx a ^ k
  | .sub .. | .neg .. | .intCast .. => 0

attribute [local simp] Ring.OfSemiring.toQ_add Ring.OfSemiring.toQ_mul Ring.OfSemiring.toQ_ofNat
  Ring.OfSemiring.toQ_pow Ring.OfSemiring.toQ_zero in
theorem Expr.denoteAsRing_eq {α} [Semiring α] (ctx : Context α) (e : Expr) : e.denoteSAsRing ctx = Ring.OfSemiring.toQ (e.denoteS ctx) := by
  induction e <;> simp [denoteS, denoteSAsRing, *]

def Expr.toPolyS : Expr → CommRing.Poly
  | .num n   => .num n.natAbs
  | .var x   => CommRing.Poly.ofVar x
  | .add a b => a.toPolyS.combine b.toPolyS
  | .mul a b => a.toPolyS.mul b.toPolyS
  | .pow a k =>
    match a with
    | .num n => .num (n.natAbs ^ k)
    | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPolyS.pow k
  | .natCast n => .num n
  | .sub .. | .neg  .. | .intCast .. => .num 0

def Expr.toPolyS_nc : Expr → CommRing.Poly
  | .num n   => .num n.natAbs
  | .var x   => CommRing.Poly.ofVar x
  | .add a b => a.toPolyS_nc.combine b.toPolyS_nc
  | .mul a b => a.toPolyS_nc.mul_nc b.toPolyS_nc
  | .pow a k =>
    match a with
    | .num n => .num (n.natAbs ^ k)
    | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPolyS_nc.pow_nc k
  | .natCast n => .num n
  | .sub .. | .neg  .. | .intCast .. => .num 0

end CommRing

namespace CommRing
attribute [local instance] Semiring.natCast Ring.intCast
open AddCommMonoid AddCommGroup
open Semiring hiding add_zero add_comm add_assoc
open Ring CommSemiring

inductive Poly.NonnegCoeffs : Poly → Prop
  | num (c : Int) : c ≥ 0 → NonnegCoeffs (.num c)
  | add (a : Int) (m : Mon) (p : Poly) : a ≥ 0 → NonnegCoeffs p → NonnegCoeffs (.add a m p)

def denoteSInt {α} [Semiring α] (k : Int) : α :=
  bif k < 0 then
    0
  else
    OfNat.ofNat (α := α) k.natAbs

theorem denoteSInt_eq {α} [Semiring α] (k : Int) : denoteSInt (α := α) k = k.toNat := by
  simp [denoteSInt, cond_eq_ite] <;> split
  next h => rw [ofNat_eq_natCast, Int.toNat_of_nonpos (Int.le_of_lt h)]
  next h =>
    have : (k.natAbs : Int) = k.toNat := by
      rw [Int.toNat_of_nonneg (Int.le_of_not_gt h), Int.natAbs_of_nonneg (Int.le_of_not_gt h)]
    rw [ofNat_eq_natCast, Int.ofNat_inj.mp this]

def Poly.denoteS [Semiring α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => denoteSInt k
  | .add k m p => denoteSInt k * m.denote ctx + denoteS ctx p

attribute [local simp] natCast_one natCast_zero zero_mul mul_zero one_mul mul_one add_zero zero_add denoteSInt_eq

theorem Poly.denoteS_ofMon {α} [Semiring α] (ctx : Context α) (m : Mon)
    : denoteS ctx (ofMon m) = m.denote ctx := by
  simp [ofMon, denoteS]

theorem Poly.denoteS_ofVar {α} [Semiring α] (ctx : Context α) (x : Var)
    : denoteS ctx (ofVar x) = x.denote ctx := by
  simp [ofVar, denoteS_ofMon, Mon.denote_ofVar]

theorem Poly.denoteS_addConst {α} [Semiring α] (ctx : Context α) (p : Poly) (k : Int)
    : k ≥ 0 → p.NonnegCoeffs → (addConst p k).denoteS ctx = p.denoteS ctx + k.toNat := by
  simp [addConst, cond_eq_ite]; split
  next => subst k; simp
  next =>
    fun_induction addConst.go <;> simp [denoteS, *]
    next c =>
      intro _ h; cases h
      rw [Int.toNat_add, natCast_add] <;> assumption
    next ih =>
      intro _ h; cases h
      next h₁ h₂ => simp [*, add_assoc]

theorem Poly.denoteS_insert {α} [Semiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (insert k m p).denoteS ctx = k.toNat * m.denote ctx + p.denoteS ctx := by
  simp [insert, cond_eq_ite] <;> split
  next => simp [*]
  next =>
    split
    next h =>
      intro _ hn
      simp at h <;> simp [*, Mon.denote, denoteS_addConst, add_comm]
    next =>
      fun_induction insert.go <;> simp_all +zetaDelta [denoteS]
      next a m p _ _ h₁ h₂ =>
        intro hk hn
        cases hn; rename_i hn₁ hn₂
        replace h₂ : k.toNat + a.toNat = 0 := by
          apply Int.ofNat_inj.mp
          rw [Int.natCast_add, Int.toNat_of_nonneg hn₁,
              Int.toNat_of_nonneg hk, h₂]; rfl
        rw [← add_assoc, Mon.eq_of_grevlex h₁, ← right_distrib, ← natCast_add, h₂]
        simp
      next h₁ _ =>
        intro _ hn; cases hn
        rw [Int.toNat_add, natCast_add, right_distrib, add_assoc, Mon.eq_of_grevlex h₁] <;> assumption
      next ih =>
        intro hk hn; cases hn; rename_i hn₁ hn₂
        rw [ih hk hn₂, add_left_comm]

theorem Poly.denoteS_concat {α} [Semiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (concat p₁ p₂).denoteS ctx = p₁.denoteS ctx + p₂.denoteS ctx := by
  fun_induction concat <;> intro h₁ h₂; simp [*, denoteS]
  next => cases h₁; rw [add_comm, denoteS_addConst] <;> assumption
  next ih => cases h₁; next hn₁ hn₂ => rw [denoteS, denoteS, ih hn₂ h₂, add_assoc]

theorem Poly.denoteS_mulConst {α} [Semiring α] (ctx : Context α) (k : Int) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (mulConst k p).denoteS ctx = k.toNat * p.denoteS ctx := by
  simp [mulConst, cond_eq_ite] <;> split
  next => simp [denoteS, *, zero_mul]
  next =>
    split <;> try simp [*]
    fun_induction mulConst.go <;> simp [denoteS, *]
    next =>
      intro _ h₂; cases h₂
      rw [Int.toNat_mul, natCast_mul] <;> assumption
    next ih =>
      intro h₁ h₂; cases h₂; rename_i h₂ h₃
      rw [Int.toNat_mul, natCast_mul, left_distrib, mul_assoc, ih h₁ h₃] <;> assumption

theorem Poly.denoteS_combine {α} [Semiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (combine p₁ p₂).denoteS ctx = p₁.denoteS ctx + p₂.denoteS ctx := by
  unfold combine; generalize hugeFuel = fuel
  fun_induction combine.go
  case case1 => intros; apply denoteS_concat <;> assumption
  case case2 => intro h₁ h₂; cases h₁; cases h₂; simp [denoteS, Int.toNat_add, natCast_add, *]
  case case3 => intro h₁ h₂; cases h₁; simp [denoteS, denoteS_addConst, add_comm, *]
  case case4 => intro h₁ h₂; cases h₂; simp [denoteS, denoteS_addConst, *]
  case case5 k₁ _ _ k₂ _ _ hg _ h ih =>
    intro h₁ h₂
    cases h₁; cases h₂
    simp +zetaDelta at h
    rename_i h₁ h₂ h₃ h₄
    simp [ih h₂ h₄, denoteS, Mon.eq_of_grevlex hg]
    replace h : k₂.toNat + k₁.toNat = 0 := by
      rw [← Int.toNat_add, Int.add_comm, h]; rfl; assumption; assumption
    rw [add_left_comm, ← add_assoc, ← add_assoc, ← right_distrib, ← natCast_add, h]
    simp
  case case6 hg k h ih =>
    intro h₁ h₂
    cases h₁; cases h₂
    simp +zetaDelta
    simp [denoteS, Int.toNat_add, natCast_add, right_distrib, Mon.eq_of_grevlex hg,
      add_left_comm, add_assoc, *]
  case case7 ih =>
    intro h₁ h₂; cases h₁
    rename_i h₁
    simp [denoteS, ih h₁ h₂, add_left_comm, add_assoc]
  case case8 ih =>
    intro h₁ h₂; cases h₂
    rename_i h₂
    simp [denoteS, ih h₁ h₂, add_left_comm, add_assoc]

theorem Poly.denoteS_mulMon {α} [CommSemiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (mulMon k m p).denoteS ctx = k.toNat * m.denote ctx * p.denoteS ctx := by
  simp [mulMon, cond_eq_ite] <;> split
  next => simp [denoteS, *]
  next =>
    split
    next h =>
      intro h₁ h₂
      simp at h; simp [*, Mon.denote, denoteS_mulConst _ _ _ h₁ h₂]
    next =>
      fun_induction mulMon.go <;> simp [denoteS, *]
      next h => simp +zetaDelta at h; simp [*]
      next =>
        intro h₁ h₂; cases h₂
        rw [Int.toNat_mul]
        simp [natCast_mul, CommSemiring.mul_comm, CommSemiring.mul_left_comm, mul_assoc]
        assumption; assumption
      next ih =>
        intro h₁ h₂; cases h₂; rename_i h₂ h₃
        rw [Int.toNat_mul]
        simp [Mon.denote_mul, natCast_mul, left_distrib, CommSemiring.mul_left_comm, mul_assoc, ih h₁ h₃]
        assumption; assumption

theorem Poly.addConst_NonnegCoeffs {p : Poly} {k : Int} : k ≥ 0 → p.NonnegCoeffs → (p.addConst k).NonnegCoeffs := by
  simp [addConst, cond_eq_ite]; split
  next => intros; assumption
  fun_induction addConst.go
  next h _ => intro _ h; cases h; constructor; apply Int.add_nonneg <;> assumption
  next ih => intro h₁ h₂; cases h₂; constructor; assumption; apply ih <;> assumption

theorem Poly.insert_Nonneg (k : Int) (m : Mon) (p : Poly) : k ≥ 0 → p.NonnegCoeffs → (p.insert k m).NonnegCoeffs := by
  intro h₁ h₂
  fun_cases Poly.insert
  next => assumption
  next => apply Poly.addConst_NonnegCoeffs <;> assumption
  next =>
    fun_induction Poly.insert.go
    next => constructor <;> assumption
    next => cases h₂; assumption
    next => simp +zetaDelta; cases h₂; constructor; omega; assumption
    next => constructor <;> assumption
    next ih =>
      cases h₂; constructor
      next => assumption
      next => apply ih; assumption

theorem Poly.denoteS_mulMon_nc_go {α} [Semiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly) (acc : Poly)
    : k ≥ 0 → p.NonnegCoeffs → acc.NonnegCoeffs
      → (mulMon_nc.go k m p acc).denoteS ctx = k.toNat * m.denote ctx * p.denoteS ctx + acc.denoteS ctx := by
  fun_induction mulMon_nc.go with simp [*]
  | case1 acc k' =>
    intro h₁ h₂ h₃; cases h₂
    have : k * k' ≥ 0 := by apply Int.mul_nonneg <;> assumption
    simp [denoteS_insert, denoteS, Int.toNat_mul, Semiring.natCast_mul, Semiring.mul_assoc, *]
    rw [← Semiring.natCast_mul_comm]
  | case2 acc k' m' p ih =>
    intro h₁ h₂ h₃; rcases h₂
    next _ h₂ =>
    have : k * k' ≥ 0 := by apply Int.mul_nonneg <;> assumption
    have : (insert (k * k') (m.mul_nc m') acc).NonnegCoeffs := by apply Poly.insert_Nonneg <;> assumption
    rw [ih h₁ h₂ this]
    simp [denoteS_insert, Int.toNat_mul, Semiring.natCast_mul, denoteS, left_distrib, Mon.denote_mul_nc, *]
    simp only [← Semiring.add_assoc]
    congr 1
    rw [Semiring.add_comm]
    congr 1
    rw [Semiring.natCast_mul_left_comm]
    conv => enter [1, 1]; rw [Semiring.natCast_mul_comm]
    simp [Semiring.mul_assoc]

theorem Poly.num_zero_NonnegCoeffs : (num 0).NonnegCoeffs := by
  apply NonnegCoeffs.num; simp

theorem Poly.denoteS_mulMon_nc {α} [Semiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (mulMon_nc k m p).denoteS ctx = k.toNat * m.denote ctx * p.denoteS ctx := by
  simp [mulMon_nc, cond_eq_ite] <;> split
  next => simp [denoteS, *]
  next =>
    split
    next h =>
      intro h₁ h₂
      simp at h; simp [*, Mon.denote, denoteS_mulConst _ _ _ h₁ h₂]
    next =>
      intro h₁ h₂
      have := Poly.denoteS_mulMon_nc_go ctx k m p (.num 0) h₁ h₂ Poly.num_zero_NonnegCoeffs
      simp [this, denoteS]

theorem Poly.mulConst_NonnegCoeffs {p : Poly} {k : Int} : k ≥ 0 → p.NonnegCoeffs → (p.mulConst k).NonnegCoeffs := by
  simp [mulConst, cond_eq_ite]; split
  next => intros; constructor; decide
  split; intros; assumption
  fun_induction mulConst.go
  next =>
    intro h₁ h₂; cases h₂; constructor
    apply Int.mul_nonneg <;> assumption
  next =>
    intro h₁ h₂; cases h₂; constructor
    apply Int.mul_nonneg <;> assumption
    next ih _ h => exact ih h₁ h

theorem Poly.mulMon_NonnegCoeffs {p : Poly} {k : Int} (m : Mon) : k ≥ 0 → p.NonnegCoeffs → (p.mulMon k m).NonnegCoeffs := by
  simp [mulMon, cond_eq_ite]; split
  next => intros; constructor; decide
  split
  next => intros; apply mulConst_NonnegCoeffs <;> assumption
  fun_induction mulMon.go
  next => intros; constructor; decide
  next => intro _ h; cases h; constructor; apply Int.mul_nonneg <;> assumption; constructor; decide
  next ih =>
    intro h₁ h₂; cases h₂; constructor
    apply Int.mul_nonneg <;> assumption
    apply ih <;> assumption

theorem Poly.mulMon_nc_go_NonnegCoeffs {p : Poly} {k : Int} (m : Mon) {acc : Poly}
    : k ≥ 0 → p.NonnegCoeffs → acc.NonnegCoeffs → (Poly.mulMon_nc.go k m p acc).NonnegCoeffs := by
  intro h₁ h₂ h₃
  fun_induction Poly.mulMon_nc.go
  next k' =>
    cases h₂
    have : k*k' ≥ 0 := by apply Int.mul_nonneg <;> assumption
    apply Poly.insert_Nonneg <;> assumption
  next ih =>
    cases h₂; next h₂ =>
    apply ih; assumption
    apply insert_Nonneg
    next => apply Int.mul_nonneg <;> assumption
    next => assumption

theorem Poly.mulMon_nc_NonnegCoeffs {p : Poly} {k : Int} (m : Mon) : k ≥ 0 → p.NonnegCoeffs → (p.mulMon_nc k m).NonnegCoeffs := by
  simp [mulMon_nc, cond_eq_ite]; split
  next => intros; constructor; decide
  split
  next => intros; apply mulConst_NonnegCoeffs <;> assumption
  intro h₁ h₂
  apply Poly.mulMon_nc_go_NonnegCoeffs; assumption; assumption
  exact Poly.num_zero_NonnegCoeffs

theorem Poly.concat_NonnegCoeffs {p₁ p₂ : Poly} : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.concat p₂).NonnegCoeffs := by
  fun_induction Poly.concat
  next => intro h₁ h₂; cases h₁; apply addConst_NonnegCoeffs <;> assumption
  next ih => intro h₁ h₂; cases h₁; constructor; assumption; apply ih <;> assumption

theorem Poly.combine_NonnegCoeffs {p₁ p₂ : Poly} : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.combine p₂).NonnegCoeffs := by
  unfold combine; generalize hugeFuel = fuel
  fun_induction combine.go
  next => intros; apply Poly.concat_NonnegCoeffs <;> assumption
  next => intro h₁ h₂; cases h₁; cases h₂; constructor; apply Int.add_nonneg <;> assumption
  next => intro h₁ h₂; apply addConst_NonnegCoeffs; cases h₁; assumption; assumption
  next => intro h₁ h₂; apply addConst_NonnegCoeffs; cases h₂; assumption; assumption
  next ih => intro h₁ h₂; cases h₁; cases h₂; apply ih <;> assumption
  next ih =>
    simp +zetaDelta; intro h₁ h₂; cases h₁; cases h₂; constructor; apply Int.add_nonneg <;> assumption
    apply ih <;> assumption
  next ih =>
    intro h₁ h₂; cases h₁; cases h₂; constructor; assumption
    apply ih; assumption
    constructor <;> assumption
  next ih =>
    intro h₁ h₂; cases h₁; cases h₂; constructor; assumption
    apply ih
    constructor <;> assumption
    assumption

theorem Poly.mul_go_NonnegCoeffs (p₁ p₂ acc : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → acc.NonnegCoeffs → (mul.go p₂ p₁ acc).NonnegCoeffs := by
  fun_induction mul.go
  next =>
    intro h₁ h₂ h₃
    cases h₁; rename_i h₁
    have := mulConst_NonnegCoeffs h₁ h₂
    apply combine_NonnegCoeffs <;> assumption
  next ih =>
    intro h₁ h₂ h₃
    cases h₁
    apply ih
    assumption; assumption
    apply Poly.combine_NonnegCoeffs; assumption
    apply Poly.mulMon_NonnegCoeffs <;> assumption

theorem Poly.mul_NonnegCoeffs {p₁ p₂ : Poly} : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.mul p₂).NonnegCoeffs := by
  unfold mul; intros; apply mul_go_NonnegCoeffs
  assumption; assumption; constructor; decide

theorem Poly.mul_nc_go_NonnegCoeffs (p₁ p₂ acc : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → acc.NonnegCoeffs → (mul_nc.go p₂ p₁ acc).NonnegCoeffs := by
  fun_induction mul_nc.go
  next =>
    intro h₁ h₂ h₃
    cases h₁; rename_i h₁
    have := mulConst_NonnegCoeffs h₁ h₂
    apply combine_NonnegCoeffs <;> assumption
  next ih =>
    intro h₁ h₂ h₃
    cases h₁
    apply ih
    assumption; assumption
    apply Poly.combine_NonnegCoeffs; assumption
    apply Poly.mulMon_nc_NonnegCoeffs <;> assumption

theorem Poly.mul_nc_NonnegCoeffs {p₁ p₂ : Poly} : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.mul_nc p₂).NonnegCoeffs := by
  unfold mul_nc; intros; apply mul_nc_go_NonnegCoeffs
  assumption; assumption; constructor; decide

theorem Poly.pow_NonnegCoeffs {p : Poly} (k : Nat) : p.NonnegCoeffs → (p.pow k).NonnegCoeffs := by
  fun_induction Poly.pow
  next => intros; constructor; decide
  next => intros; assumption
  next ih => intro h; apply mul_NonnegCoeffs; assumption; apply ih; assumption

theorem Poly.pow_nc_NonnegCoeffs {p : Poly} (k : Nat) : p.NonnegCoeffs → (p.pow_nc k).NonnegCoeffs := by
  fun_induction Poly.pow_nc
  next => intros; constructor; decide
  next => intros; assumption
  next ih =>
    intro h; apply mul_nc_NonnegCoeffs
    next => apply ih; assumption
    next => assumption

theorem Poly.denoteS_mul_go {α} [CommSemiring α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → acc.NonnegCoeffs → (mul.go p₂ p₁ acc).denoteS ctx = acc.denoteS ctx + p₁.denoteS ctx * p₂.denoteS ctx := by
  fun_induction mul.go <;> intro h₁ h₂ h₃
  next k =>
    cases h₁; rename_i h₁
    have := p₂.mulConst_NonnegCoeffs h₁ h₂
    simp [denoteS, denoteS_combine, denoteS_mulConst, *]
  next acc a m p ih =>
    cases h₁; rename_i h₁ h₁'
    have := p₂.mulMon_NonnegCoeffs m h₁ h₂
    have := acc.combine_NonnegCoeffs h₃ this
    replace ih := ih h₁' h₂ this
    rw [ih, denoteS_combine, denoteS_mulMon]
    simp [denoteS, add_assoc, right_distrib]
    all_goals assumption

theorem Poly.denoteS_mul {α} [CommSemiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (mul p₁ p₂).denoteS ctx = p₁.denoteS ctx * p₂.denoteS ctx := by
  intro h₁ h₂
  simp [mul, denoteS_mul_go, denoteS, Poly.num_zero_NonnegCoeffs, *]

theorem Poly.denoteS_mul_nc_go {α} [Semiring α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → acc.NonnegCoeffs → (mul_nc.go p₂ p₁ acc).denoteS ctx = acc.denoteS ctx + p₁.denoteS ctx * p₂.denoteS ctx := by
  fun_induction mul_nc.go <;> intro h₁ h₂ h₃
  next k =>
    cases h₁; rename_i h₁
    have := p₂.mulConst_NonnegCoeffs h₁ h₂
    simp [denoteS, denoteS_combine, denoteS_mulConst, *]
  next acc a m p ih =>
    cases h₁; rename_i h₁ h₁'
    have := p₂.mulMon_nc_NonnegCoeffs m h₁ h₂
    have := acc.combine_NonnegCoeffs h₃ this
    replace ih := ih h₁' h₂ this
    rw [ih, denoteS_combine, denoteS_mulMon_nc]
    simp [denoteS, add_assoc, right_distrib]
    all_goals assumption

theorem Poly.denoteS_mul_nc {α} [Semiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (mul_nc p₁ p₂).denoteS ctx = p₁.denoteS ctx * p₂.denoteS ctx := by
  intro h₁ h₂
  simp [mul_nc, denoteS_mul_nc_go, denoteS, Poly.num_zero_NonnegCoeffs, *]

theorem Poly.denoteS_pow {α} [CommSemiring α] (ctx : Context α) (p : Poly) (k : Nat)
   : p.NonnegCoeffs → (pow p k).denoteS ctx = p.denoteS ctx ^ k := by
 fun_induction pow <;> intro h₁
 next => simp [denoteS, pow_zero]
 next => simp [pow_succ, pow_zero]
 next ih =>
  replace ih := ih h₁
  rw [denoteS_mul, ih, pow_succ, CommSemiring.mul_comm]
  assumption
  apply Poly.pow_NonnegCoeffs; assumption

theorem Poly.denoteS_pow_nc {α} [Semiring α] (ctx : Context α) (p : Poly) (k : Nat)
   : p.NonnegCoeffs → (pow_nc p k).denoteS ctx = p.denoteS ctx ^ k := by
 fun_induction pow_nc <;> intro h₁
 next => simp [denoteS, pow_zero]
 next => simp [pow_succ, pow_zero]
 next ih =>
  replace ih := ih h₁
  rw [denoteS_mul_nc, ih, pow_succ]
  apply Poly.pow_nc_NonnegCoeffs; assumption
  assumption

theorem Expr.toPolyS_NonnegCoeffs {e : Expr} : e.toPolyS.NonnegCoeffs := by
  fun_induction toPolyS
  next => constructor; apply Int.natCast_nonneg
  next => simp [Poly.ofVar, Poly.ofMon]; constructor; decide; constructor; decide
  next => apply Poly.combine_NonnegCoeffs <;> assumption
  next => apply Poly.mul_NonnegCoeffs <;> assumption
  next => constructor; apply Int.pow_nonneg; apply Int.natCast_nonneg
  next => constructor; decide; constructor; decide
  next => apply Poly.pow_NonnegCoeffs; assumption
  next => constructor; apply Int.natCast_nonneg
  all_goals exact Poly.num_zero_NonnegCoeffs

attribute [local simp] Expr.toPolyS_NonnegCoeffs

theorem Expr.toPolyS_nc_NonnegCoeffs {e : Expr} : e.toPolyS_nc.NonnegCoeffs := by
  fun_induction toPolyS_nc
  next => constructor; apply Int.natCast_nonneg
  next => simp [Poly.ofVar, Poly.ofMon]; constructor; decide; constructor; decide
  next => apply Poly.combine_NonnegCoeffs <;> assumption
  next => apply Poly.mul_nc_NonnegCoeffs <;> assumption
  next => constructor; apply Int.pow_nonneg; apply Int.natCast_nonneg
  next => constructor; decide; constructor; decide
  next => apply Poly.pow_nc_NonnegCoeffs; assumption
  next => constructor; apply Int.natCast_nonneg
  all_goals exact Poly.num_zero_NonnegCoeffs

attribute [local simp] Expr.toPolyS_nc_NonnegCoeffs

theorem Expr.denoteS_toPolyS {α} [CommSemiring α] (ctx : Context α) (e : Expr)
   : e.toPolyS.denoteS ctx = e.denoteS ctx := by
  fun_induction toPolyS <;> simp [denoteS, Poly.denoteS, Poly.denoteS_ofVar, denoteSInt_eq]
  next => simp [Semiring.ofNat_eq_natCast]
  next => simp [Poly.denoteS_combine] <;> simp [*]
  next => simp [Poly.denoteS_mul] <;> simp [*]
  next => rw [Int.toNat_pow_of_nonneg, Semiring.natCast_pow, Int.toNat_natCast, ← Semiring.ofNat_eq_natCast]
          apply Int.natCast_nonneg
  next => simp [Poly.ofMon, Poly.denoteS, denoteSInt_eq, Power.denote_eq, Mon.denote,
                Semiring.natCast_zero, Semiring.natCast_one, Semiring.one_mul,
                CommRing.Var.denote, Var.denote, Semiring.mul_one]
  next ih => rw [Poly.denoteS_pow, ih]; apply toPolyS_NonnegCoeffs
  next => simp [Semiring.natCast_eq_ofNat]

theorem Expr.denoteS_toPolyS_nc {α} [Semiring α] (ctx : Context α) (e : Expr)
   : e.toPolyS_nc.denoteS ctx = e.denoteS ctx := by
  fun_induction Expr.toPolyS_nc <;> simp [denoteS, Poly.denoteS, Poly.denoteS_ofVar, denoteSInt_eq]
  next => simp [Semiring.ofNat_eq_natCast]
  next => simp [Poly.denoteS_combine] <;> simp [*]
  next => simp [Poly.denoteS_mul_nc] <;> simp [*]
  next => rw [Int.toNat_pow_of_nonneg, Semiring.natCast_pow, Int.toNat_natCast, ← Semiring.ofNat_eq_natCast]
          apply Int.natCast_nonneg
  next => simp [Poly.ofMon, Poly.denoteS, denoteSInt_eq, Power.denote_eq, Mon.denote,
                Semiring.natCast_zero, Semiring.natCast_one, Semiring.one_mul,
                CommRing.Var.denote, Var.denote, Semiring.mul_one]
  next ih => rw [Poly.denoteS_pow_nc, ih]; apply toPolyS_nc_NonnegCoeffs
  next => simp [Semiring.natCast_eq_ofNat]

def eq_normS_cert (lhs rhs : Expr) : Bool :=
  lhs.toPolyS == rhs.toPolyS

theorem eq_normS {α} [CommSemiring α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normS_cert lhs rhs → lhs.denoteS ctx = rhs.denoteS ctx := by
  simp [eq_normS_cert]; intro h
  replace h := congrArg (Poly.denoteS ctx) h
  simp [Expr.denoteS_toPolyS, *] at h
  assumption

def eq_normS_nc_cert (lhs rhs : Expr) : Bool :=
  lhs.toPolyS_nc == rhs.toPolyS_nc

theorem eq_normS_nc {α} [Semiring α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normS_nc_cert lhs rhs → lhs.denoteS ctx = rhs.denoteS ctx := by
  simp [eq_normS_nc_cert]; intro h
  replace h := congrArg (Poly.denoteS ctx) h
  simp [Expr.denoteS_toPolyS_nc, *] at h
  assumption

end CommRing

namespace Ring.OfSemiring
open CommRing

theorem of_eq {α} [Semiring α] (ctx : Context α) (lhs rhs : Expr)
    : lhs.denoteS ctx = rhs.denoteS ctx → lhs.denoteSAsRing ctx = rhs.denoteSAsRing ctx := by
  intro h; replace h := congrArg toQ h
  simpa [← Expr.denoteAsRing_eq] using h

theorem of_diseq {α} [Semiring α] [AddRightCancel α] (ctx : Context α) (lhs rhs : Expr)
    : lhs.denoteS ctx ≠ rhs.denoteS ctx → lhs.denoteSAsRing ctx ≠ rhs.denoteSAsRing ctx := by
  intro h₁ h₂
  simp [Expr.denoteAsRing_eq] at h₂
  replace h₂ := toQ_inj h₂
  contradiction

end Ring.OfSemiring
end Lean.Grind
