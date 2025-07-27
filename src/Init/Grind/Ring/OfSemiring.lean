/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Ring.Envelope
public import Init.Data.Hashable
public import Init.Data.RArray
public import all Init.Grind.Ring.Poly

public section

namespace Lean.Grind.Ring.OfSemiring
/-!
Helper definitions and theorems for converting `Semiring` expressions into `Ring` ones.
We use them to implement `grind`
-/
abbrev Var := Nat
inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (k : Nat)
  deriving Inhabited, BEq, Hashable

abbrev Context (α : Type u) := RArray α

def Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

def Expr.denote {α} [Semiring α] (ctx : Context α) : Expr → α
  | .num k    => OfNat.ofNat (α := α) k
  | .var v    => v.denote ctx
  | .add a b  => denote ctx a + denote ctx b
  | .mul a b  => denote ctx a * denote ctx b
  | .pow a k  => denote ctx a ^ k

attribute [local instance] ofSemiring

def Expr.denoteAsRing {α} [Semiring α] (ctx : Context α) : Expr → Q α
  | .num k    => OfNat.ofNat (α := Q α) k
  | .var v    => toQ (v.denote ctx)
  | .add a b  => denoteAsRing ctx a + denoteAsRing ctx b
  | .mul a b  => denoteAsRing ctx a * denoteAsRing ctx b
  | .pow a k  => denoteAsRing ctx a ^ k

attribute [local simp] toQ_add toQ_mul toQ_ofNat toQ_pow

theorem Expr.denoteAsRing_eq {α} [Semiring α] (ctx : Context α) (e : Expr) : e.denoteAsRing ctx = toQ (e.denote ctx) := by
  induction e <;> simp [denote, denoteAsRing, *]

theorem of_eq {α} [Semiring α] (ctx : Context α) (lhs rhs : Expr)
    : lhs.denote ctx = rhs.denote ctx → lhs.denoteAsRing ctx = rhs.denoteAsRing ctx := by
  intro h; replace h := congrArg toQ h
  simpa [← Expr.denoteAsRing_eq] using h

theorem of_diseq {α} [Semiring α] [AddRightCancel α] (ctx : Context α) (lhs rhs : Expr)
    : lhs.denote ctx ≠ rhs.denote ctx → lhs.denoteAsRing ctx ≠ rhs.denoteAsRing ctx := by
  intro h₁ h₂
  simp [Expr.denoteAsRing_eq] at h₂
  replace h₂ := toQ_inj h₂
  contradiction

def Expr.toPoly : Expr → CommRing.Poly
  | .num n   => .num n
  | .var x   => CommRing.Poly.ofVar x
  | .add a b => a.toPoly.combine b.toPoly
  | .mul a b => a.toPoly.mul b.toPoly
  | .pow a k =>
    match a with
    | .num n => .num (n^k)
    | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPoly.pow k

end Ring.OfSemiring

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
  simp [denoteSInt, cond_eq_if] <;> split
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

theorem Poly.denoteS_ofMon {α} [CommSemiring α] (ctx : Context α) (m : Mon)
    : denoteS ctx (ofMon m) = m.denote ctx := by
  simp [ofMon, denoteS]

theorem Poly.denoteS_ofVar {α} [CommSemiring α] (ctx : Context α) (x : Var)
    : denoteS ctx (ofVar x) = x.denote ctx := by
  simp [ofVar, denoteS_ofMon, Mon.denote_ofVar]

theorem Poly.denoteS_addConst {α} [CommSemiring α] (ctx : Context α) (p : Poly) (k : Int)
    : k ≥ 0 → p.NonnegCoeffs → (addConst p k).denoteS ctx = p.denoteS ctx + k.toNat := by
  simp [addConst, cond_eq_if]; split
  next => subst k; simp
  next =>
    fun_induction addConst.go <;> simp [denoteS, *]
    next c =>
      intro _ h; cases h
      rw [Int.toNat_add, natCast_add] <;> assumption
    next ih =>
      intro _ h; cases h
      next h₁ h₂ => simp [*, add_assoc]

theorem Poly.denoteS_insert {α} [CommSemiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (insert k m p).denoteS ctx = k.toNat * m.denote ctx + p.denoteS ctx := by
  simp [insert, cond_eq_if] <;> split
  next => simp [*]
  next =>
    split
    next h =>
      intro _ hn
      simp at h <;> simp [*, Mon.denote, denoteS_addConst, add_comm]
    next =>
      fun_induction insert.go <;> simp_all +zetaDelta [denoteS]
      next h₁ h₂ =>
        intro _ hn; cases hn
        next a m p _ _ hk hn₁ hn₂ =>
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
        intro hk hn; cases hn
        next hn₁ hn₂ =>
        rw [ih hk hn₂, add_left_comm]

theorem Poly.denoteS_concat {α} [CommSemiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (concat p₁ p₂).denoteS ctx = p₁.denoteS ctx + p₂.denoteS ctx := by
  fun_induction concat <;> intro h₁ h₂; simp [*, denoteS]
  next => cases h₁; rw [add_comm, denoteS_addConst] <;> assumption
  next ih => cases h₁; next hn₁ hn₂ => rw [denoteS, denoteS, ih hn₂ h₂, add_assoc]

theorem Poly.denoteS_mulConst {α} [CommSemiring α] (ctx : Context α) (k : Int) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (mulConst k p).denoteS ctx = k.toNat * p.denoteS ctx := by
  simp [mulConst, cond_eq_if] <;> split
  next => simp [denoteS, *, zero_mul]
  next =>
    split <;> try simp [*]
    fun_induction mulConst.go <;> simp [denoteS, *]
    next =>
      intro _ h₂; cases h₂
      rw [Int.toNat_mul, natCast_mul] <;> assumption
    next =>
      intro _ h₂; cases h₂
      next ih h₁ h₂ h₃ =>
      rw [Int.toNat_mul, natCast_mul, left_distrib, mul_assoc, ih h₁ h₃] <;> assumption

theorem Poly.denoteS_mulMon {α} [CommSemiring α] (ctx : Context α) (k : Int) (m : Mon) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (mulMon k m p).denoteS ctx = k.toNat * m.denote ctx * p.denoteS ctx := by
  simp [mulMon, cond_eq_if] <;> split
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
      next =>
        intro h₁ h₂; cases h₂
        next ih h₂ h₃ =>
        rw [Int.toNat_mul]
        simp [Mon.denote_mul, natCast_mul, left_distrib, CommSemiring.mul_left_comm, mul_assoc, ih h₁ h₃]
        assumption; assumption

theorem Poly.denoteS_combine {α} [CommSemiring α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (combine p₁ p₂).denoteS ctx = p₁.denoteS ctx + p₂.denoteS ctx := by
  unfold combine; generalize hugeFuel = fuel
  fun_induction combine.go
  case case1 => intros; apply denoteS_concat <;> assumption
  case case2 => intros h₁ h₂; cases h₁; cases h₂; simp [denoteS, Int.toNat_add, natCast_add, *]
  case case3 => intro h₁ h₂; cases h₁; simp [denoteS, denoteS_addConst, add_comm, *]
  case case4 => intro h₁ h₂; cases h₂; simp [denoteS, denoteS_addConst, *]
  case case5 k₁ _ _ k₂ _ _ hg _ h _ =>
    intro h₁ h₂
    cases h₁; cases h₂
    simp +zetaDelta at h
    next ih h₁ h₂ h₃ h₄ =>
    simp [ih h₂ h₄, denoteS, Mon.eq_of_grevlex hg]
    replace h : k₂.toNat + k₁.toNat = 0 := by
      rw [← Int.toNat_add, Int.add_comm, h]; rfl; assumption; assumption
    rw [add_left_comm, ← add_assoc, ← add_assoc, ← right_distrib, ← natCast_add, h]
    simp
  case case6 hg k h _ =>
    intro h₁ h₂
    cases h₁; cases h₂
    simp +zetaDelta
    next ih h₁ h₂ h₃ h₄ =>
    simp [denoteS, Int.toNat_add, natCast_add, right_distrib, Mon.eq_of_grevlex hg,
      add_left_comm, add_assoc, *]
  case case7 =>
    intro h₁ h₂; cases h₁
    next ih _ h₁ =>
    simp [denoteS, ih h₁ h₂, add_left_comm, add_assoc]
  case case8 =>
    intro h₁ h₂; cases h₂
    next ih _ h₂ =>
    simp [denoteS, ih h₁ h₂, add_left_comm, add_assoc]

theorem Poly.mulConst_NonnegCoeffs {p : Poly} {k : Int} : k ≥ 0 → p.NonnegCoeffs → (p.mulConst k).NonnegCoeffs := by
  simp [mulConst, cond_eq_if]; split
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
  simp [mulMon, cond_eq_if]; split
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

theorem Poly.addConst_NonnegCoeffs {p : Poly} {k : Int} : k ≥ 0 → p.NonnegCoeffs → (p.addConst k).NonnegCoeffs := by
  simp [addConst, cond_eq_if]; split
  next => intros; assumption
  fun_induction addConst.go
  next h _ => intro _ h; cases h; constructor; apply Int.add_nonneg <;> assumption
  next ih => intro h₁ h₂; cases h₂; constructor; assumption; apply ih <;> assumption

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
    cases h₁; next h₁ =>
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

theorem Poly.pow_NonnegCoeffs {p : Poly} (k : Nat) : p.NonnegCoeffs → (p.pow k).NonnegCoeffs := by
  fun_induction Poly.pow
  next => intros; constructor; decide
  next => intros; assumption
  next ih => intro h; apply mul_NonnegCoeffs; assumption; apply ih; assumption

theorem Poly.num_zero_NonnegCoeffs : (num 0).NonnegCoeffs := by
  apply NonnegCoeffs.num; simp

theorem Poly.denoteS_mul_go {α} [CommSemiring α] (ctx : Context α) (p₁ p₂ acc : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → acc.NonnegCoeffs → (mul.go p₂ p₁ acc).denoteS ctx = acc.denoteS ctx + p₁.denoteS ctx * p₂.denoteS ctx := by
  fun_induction mul.go <;> intro h₁ h₂ h₃
  next k =>
    cases h₁; next h₁ =>
    have := p₂.mulConst_NonnegCoeffs h₁ h₂
    simp [denoteS, denoteS_combine, denoteS_mulConst, *]
  next acc a m p ih =>
    cases h₁; next h₁ h₁' =>
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

end CommRing

namespace Ring.OfSemiring
open CommRing

theorem Expr.toPoly_NonnegCoeffs {e : Expr} : e.toPoly.NonnegCoeffs := by
  fun_induction toPoly
  next => constructor; apply Int.natCast_nonneg
  next => simp [Poly.ofVar, Poly.ofMon]; constructor; decide; constructor; decide
  next => apply Poly.combine_NonnegCoeffs <;> assumption
  next => apply Poly.mul_NonnegCoeffs <;> assumption
  next => constructor; apply Int.pow_nonneg; apply Int.natCast_nonneg
  next => constructor; decide; constructor; decide
  next => apply Poly.pow_NonnegCoeffs; assumption

theorem Expr.denoteS_toPoly {α} [CommSemiring α] (ctx : Context α) (e : Expr)
   : e.toPoly.denoteS ctx = e.denote ctx := by
  fun_induction toPoly
    <;> simp [denote, Poly.denoteS, Poly.denoteS_ofVar, denoteSInt_eq, Semiring.ofNat_eq_natCast]
  next => simp [CommRing.Var.denote, Var.denote]
  next ih₁ ih₂ => rw [Poly.denoteS_combine, ih₁, ih₂] <;> apply toPoly_NonnegCoeffs
  next ih₁ ih₂ => rw [Poly.denoteS_mul, ih₁, ih₂] <;> apply toPoly_NonnegCoeffs
  next => rw [Int.toNat_pow_of_nonneg, Semiring.natCast_pow, Int.toNat_natCast]; apply Int.natCast_nonneg
  next =>
    simp [Poly.ofMon, Poly.denoteS, denoteSInt_eq, Power.denote_eq, Mon.denote,
          Semiring.natCast_zero, Semiring.natCast_one, Semiring.one_mul, Semiring.add_zero,
          CommRing.Var.denote, Var.denote, Semiring.mul_one]
  next ih => rw [Poly.denoteS_pow, ih]; apply toPoly_NonnegCoeffs

def eq_normS_cert (lhs rhs : Expr) : Bool :=
  lhs.toPoly == rhs.toPoly

theorem eq_normS {α} [CommSemiring α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normS_cert lhs rhs → lhs.denote ctx = rhs.denote ctx := by
  simp [eq_normS_cert]; intro h
  replace h := congrArg (Poly.denoteS ctx) h
  simp [Expr.denoteS_toPoly, *] at h
  assumption

end Lean.Grind.Ring.OfSemiring
