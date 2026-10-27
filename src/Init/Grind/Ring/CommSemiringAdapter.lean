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

noncomputable abbrev Expr.denoteS {α} [Semiring α] (ctx : Context α) (e : Expr) : α :=
  Expr.rec
    (fun k => OfNat.ofNat (α := α) k.natAbs)
    (fun k => OfNat.ofNat (α := α) k)
    (fun _ => 0)
    (fun v => v.denote ctx)
    (fun _ _ => 0)
    (fun _ _ ih₁ ih₂ => ih₁ + ih₂)
    (fun _ _ _ _ => 0)
    (fun _ _ ih₁ ih₂ => ih₁ * ih₂)
    (fun _ k ih => ih ^ k)
    e

set_option allowUnsafeReducibility true in
attribute [semireducible] Expr.denoteS

section
variable {α} [Semiring α] (ctx : Context α)
theorem Expr.denoteS_num (k : Int) : (Expr.num k).denoteS ctx = OfNat.ofNat (α := α) k.natAbs := rfl
theorem Expr.denoteS_natCast (k : Nat) : (Expr.natCast k).denoteS ctx = OfNat.ofNat (α := α) k := rfl
theorem Expr.denoteS_intCast (k : Int) : (Expr.intCast k).denoteS ctx = 0 := rfl
theorem Expr.denoteS_var (v : Var) : (Expr.var v).denoteS ctx = v.denote ctx := rfl
theorem Expr.denoteS_neg (a : Expr) : (Expr.neg a).denoteS ctx = 0 := rfl
theorem Expr.denoteS_add (a b : Expr) : (Expr.add a b).denoteS ctx = a.denoteS ctx + b.denoteS ctx := rfl
theorem Expr.denoteS_sub (a b : Expr) : (Expr.sub a b).denoteS ctx = 0 := rfl
theorem Expr.denoteS_mul (a b : Expr) : (Expr.mul a b).denoteS ctx = a.denoteS ctx * b.denoteS ctx := rfl
theorem Expr.denoteS_pow (a : Expr) (k : Nat) : (Expr.pow a k).denoteS ctx = a.denoteS ctx ^ k := rfl
end

noncomputable abbrev Expr.denoteSAsRing {α} [Semiring α] (ctx : Context α) (e : Expr) : Ring.OfSemiring.Q α :=
  Expr.rec
    (fun k => OfNat.ofNat (α := Ring.OfSemiring.Q α) k.natAbs)
    (fun k => OfNat.ofNat (α := Ring.OfSemiring.Q α) k)
    (fun _ => 0)
    (fun v => Ring.OfSemiring.toQ (v.denote ctx))
    (fun _ _ => 0)
    (fun _ _ ih₁ ih₂ => ih₁ + ih₂)
    (fun _ _ _ _ => 0)
    (fun _ _ ih₁ ih₂ => ih₁ * ih₂)
    (fun _ k ih => ih ^ k)
    e

set_option allowUnsafeReducibility true in
attribute [semireducible] Expr.denoteSAsRing

attribute [local simp] Ring.OfSemiring.toQ_add Ring.OfSemiring.toQ_mul Ring.OfSemiring.toQ_ofNat
  Ring.OfSemiring.toQ_pow Ring.OfSemiring.toQ_zero in
theorem Expr.denoteAsRing_eq {α} [Semiring α] (ctx : Context α) (e : Expr) : e.denoteSAsRing ctx = Ring.OfSemiring.toQ (e.denoteS ctx) := by
  induction e with
  | num k => show OfNat.ofNat _ = Ring.OfSemiring.toQ (OfNat.ofNat _); simp
  | natCast k => show OfNat.ofNat _ = Ring.OfSemiring.toQ (OfNat.ofNat _); simp
  | intCast k => show (0 : Ring.OfSemiring.Q α) = Ring.OfSemiring.toQ 0; simp
  | var v => rfl
  | neg a _ => show (0 : Ring.OfSemiring.Q α) = Ring.OfSemiring.toQ 0; simp
  | add a b iha ihb =>
    show a.denoteSAsRing ctx + b.denoteSAsRing ctx = Ring.OfSemiring.toQ (a.denoteS ctx + b.denoteS ctx); simp [iha, ihb]
  | sub a b _ _ => show (0 : Ring.OfSemiring.Q α) = Ring.OfSemiring.toQ 0; simp
  | mul a b iha ihb =>
    show a.denoteSAsRing ctx * b.denoteSAsRing ctx = Ring.OfSemiring.toQ (a.denoteS ctx * b.denoteS ctx); simp [iha, ihb]
  | pow a k ih => show a.denoteSAsRing ctx ^ k = Ring.OfSemiring.toQ (a.denoteS ctx ^ k); simp [ih]

def Expr.toPolyS : Expr → CommRing.Poly
  | .num n   => .num n.natAbs
  | .var x   => CommRing.Poly.ofVar x
  | .add a b => a.toPolyS.combine b.toPolyS
  | .mul a b => a.toPolyS.mul b.toPolyS
  | .pow a k =>
    bif k == 0 then
      .num 1
    else match a with
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
    bif k == 0 then
      .num 1
    else match a with
    | .num n => .num (n.natAbs ^ k)
    | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
    | _ => a.toPolyS_nc.pow_nc k
  | .natCast n => .num n
  | .sub .. | .neg  .. | .intCast .. => .num 0


noncomputable def Expr.toPolyS_k (e : Expr) : CommRing.Poly :=
  Expr.rec
    (fun n => .num (Int.ofNat (Int.natAbs_k n))) (fun n => .num (Int.ofNat n)) (fun _ => .num 0)
    (fun x => CommRing.Poly.ofVar x)
    (fun _ _ => .num 0)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ _ _ => .num 0)
    (fun _ _ ih₁ ih₂ => ih₁.mul_k ih₂)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.ofNat (Nat.pow (Int.natAbs_k n) k)))
        (fun _ => ih.pow_k k) (fun _ => ih.pow_k k)
        (fun x => CommRing.Poly.ofMon (.mult {x, k} .unit)) (fun _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ _ => ih.pow_k k)
        (fun _ _ _ => ih.pow_k k)
        a)
      (.num 1)
      (k.beq 0))
    e

@[simp] theorem Expr.toPolyS_k_eq_toPolyS (e : Expr) : e.toPolyS_k = e.toPolyS := by
  induction e with
  | num n => show CommRing.Poly.num (Int.ofNat (Int.natAbs_k n)) = _; simp [toPolyS]
  | natCast n => rfl
  | intCast n => rfl
  | var x => rfl
  | neg a ih => rfl
  | sub a b iha ihb => rfl
  | add a b iha ihb => show a.toPolyS_k.combine_k b.toPolyS_k = _; rw [iha, ihb, CommRing.Poly.combine_k_eq_combine]; rfl
  | mul a b iha ihb => show a.toPolyS_k.mul_k b.toPolyS_k = _; rw [iha, ihb, CommRing.Poly.mul_k_eq_mul]; rfl
  | pow a k ih =>
    simp only [toPolyS, cond_eq_ite]
    split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; show Bool.rec (motive := fun _ => CommRing.Poly) _ _ (k.beq 0) = _; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h
      show Bool.rec (motive := fun _ => CommRing.Poly) _ _ (k.beq 0) = _
      rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.ofNat (Nat.pow (Int.natAbs_k n) k)))
          (fun _ => a.toPolyS_k.pow_k k) (fun _ => a.toPolyS_k.pow_k k)
          (fun x => CommRing.Poly.ofMon (.mult {x, k} .unit)) (fun _ _ => a.toPolyS_k.pow_k k)
          (fun _ _ _ _ => a.toPolyS_k.pow_k k)
          (fun _ _ _ _ => a.toPolyS_k.pow_k k)
          (fun _ _ _ _ => a.toPolyS_k.pow_k k)
          (fun _ _ _ => a.toPolyS_k.pow_k k)
          a) = match a with
            | .num n => CommRing.Poly.num (n.natAbs ^ k)
            | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
            | _ => a.toPolyS.pow k
      cases a <;> simp [*, CommRing.Poly.pow_k_eq_pow] <;> rfl

noncomputable def Expr.toPolyS_nc_k (e : Expr) : CommRing.Poly :=
  Expr.rec
    (fun n => .num (Int.ofNat (Int.natAbs_k n))) (fun n => .num (Int.ofNat n)) (fun _ => .num 0)
    (fun x => CommRing.Poly.ofVar x)
    (fun _ _ => .num 0)
    (fun _ _ ih₁ ih₂ => ih₁.combine_k ih₂)
    (fun _ _ _ _ => .num 0)
    (fun _ _ ih₁ ih₂ => ih₁.mul_nc_k ih₂)
    (fun a k ih => Bool.rec
      (Expr.rec (fun n => .num (Int.ofNat (Nat.pow (Int.natAbs_k n) k)))
        (fun _ => ih.pow_nc_k k) (fun _ => ih.pow_nc_k k)
        (fun x => CommRing.Poly.ofMon (.mult {x, k} .unit)) (fun _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ _ => ih.pow_nc_k k)
        (fun _ _ _ => ih.pow_nc_k k)
        a)
      (.num 1)
      (k.beq 0))
    e

@[simp] theorem Expr.toPolyS_nc_k_eq_toPolyS_nc (e : Expr) : e.toPolyS_nc_k = e.toPolyS_nc := by
  induction e with
  | num n => show CommRing.Poly.num (Int.ofNat (Int.natAbs_k n)) = _; simp [toPolyS_nc]
  | natCast n => rfl
  | intCast n => rfl
  | var x => rfl
  | neg a ih => rfl
  | sub a b iha ihb => rfl
  | add a b iha ihb => show a.toPolyS_nc_k.combine_k b.toPolyS_nc_k = _; rw [iha, ihb, CommRing.Poly.combine_k_eq_combine]; rfl
  | mul a b iha ihb => show a.toPolyS_nc_k.mul_nc_k b.toPolyS_nc_k = _; rw [iha, ihb, CommRing.Poly.mul_nc_k_eq_mul_nc]; rfl
  | pow a k ih =>
    simp only [toPolyS_nc, cond_eq_ite]
    split
    next h => rw [Nat.beq_eq_true_eq, ← Nat.beq_eq] at h; show Bool.rec (motive := fun _ => CommRing.Poly) _ _ (k.beq 0) = _; rw [h]
    next h =>
      rw [Nat.beq_eq_true_eq, ← Nat.beq_eq, Bool.not_eq_true] at h
      show Bool.rec (motive := fun _ => CommRing.Poly) _ _ (k.beq 0) = _
      rw [h]; dsimp only
      show
        (Expr.rec (fun n => .num (Int.ofNat (Nat.pow (Int.natAbs_k n) k)))
          (fun _ => a.toPolyS_nc_k.pow_nc_k k) (fun _ => a.toPolyS_nc_k.pow_nc_k k)
          (fun x => CommRing.Poly.ofMon (.mult {x, k} .unit)) (fun _ _ => a.toPolyS_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPolyS_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPolyS_nc_k.pow_nc_k k)
          (fun _ _ _ _ => a.toPolyS_nc_k.pow_nc_k k)
          (fun _ _ _ => a.toPolyS_nc_k.pow_nc_k k)
          a) = match a with
            | .num n => CommRing.Poly.num (n.natAbs ^ k)
            | .var x => CommRing.Poly.ofMon (.mult {x, k} .unit)
            | _ => a.toPolyS_nc.pow_nc k
      cases a <;> simp [*, CommRing.Poly.pow_nc_k_eq_pow_nc] <;> rfl

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
  unfold combine; generalize p₁.length + p₂.length + 1 = fuel
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
  unfold combine; generalize p₁.length + p₂.length + 1 = fuel
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
  next => constructor; decide
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
  next => constructor; decide
  next => constructor; apply Int.pow_nonneg; apply Int.natCast_nonneg
  next => constructor; decide; constructor; decide
  next => apply Poly.pow_nc_NonnegCoeffs; assumption
  next => constructor; apply Int.natCast_nonneg
  all_goals exact Poly.num_zero_NonnegCoeffs

attribute [local simp] Expr.toPolyS_nc_NonnegCoeffs

theorem Expr.denoteS_toPolyS {α} [CommSemiring α] (ctx : Context α) (e : Expr)
   : e.toPolyS.denoteS ctx = e.denoteS ctx := by
  fun_induction toPolyS <;> simp [denoteS_num, denoteS_natCast, denoteS_intCast, denoteS_var, denoteS_neg, denoteS_add, denoteS_sub, denoteS_mul, denoteS_pow, Poly.denoteS, Poly.denoteS_ofVar, denoteSInt_eq]
  next => simp [Semiring.ofNat_eq_natCast]
  next => simp [Poly.denoteS_combine] <;> simp [*]
  next => simp [Poly.denoteS_mul] <;> simp [*]
  next => rename_i h; simp at h; simp [h, Semiring.pow_zero]
  next => rw [Int.toNat_pow_of_nonneg, Semiring.natCast_pow, Int.toNat_natCast, ← Semiring.ofNat_eq_natCast]
          apply Int.natCast_nonneg
  next => simp [Poly.ofMon, Poly.denoteS, denoteSInt_eq, Power.denote_eq, Mon.denote,
                Semiring.natCast_zero, Semiring.natCast_one, Semiring.one_mul,
                CommRing.Var.denote, Var.denote, Semiring.mul_one]
  next ih => rw [Poly.denoteS_pow, ih]; apply toPolyS_NonnegCoeffs
  next => simp [Semiring.natCast_eq_ofNat]

theorem Expr.denoteS_toPolyS_nc {α} [Semiring α] (ctx : Context α) (e : Expr)
   : e.toPolyS_nc.denoteS ctx = e.denoteS ctx := by
  fun_induction Expr.toPolyS_nc <;> simp [denoteS_num, denoteS_natCast, denoteS_intCast, denoteS_var, denoteS_neg, denoteS_add, denoteS_sub, denoteS_mul, denoteS_pow, Poly.denoteS, Poly.denoteS_ofVar, denoteSInt_eq]
  next => simp [Semiring.ofNat_eq_natCast]
  next => simp [Poly.denoteS_combine] <;> simp [*]
  next => simp [Poly.denoteS_mul_nc] <;> simp [*]
  next => rename_i h; simp at h; simp [h, Semiring.pow_zero]
  next => rw [Int.toNat_pow_of_nonneg, Semiring.natCast_pow, Int.toNat_natCast, ← Semiring.ofNat_eq_natCast]
          apply Int.natCast_nonneg
  next => simp [Poly.ofMon, Poly.denoteS, denoteSInt_eq, Power.denote_eq, Mon.denote,
                Semiring.natCast_zero, Semiring.natCast_one, Semiring.one_mul,
                CommRing.Var.denote, Var.denote, Semiring.mul_one]
  next ih => rw [Poly.denoteS_pow_nc, ih]; apply toPolyS_nc_NonnegCoeffs
  next => simp [Semiring.natCast_eq_ofNat]

noncomputable def eq_normS_cert (lhs rhs : Expr) : Bool :=
  lhs.toPolyS_k.beq' rhs.toPolyS_k

theorem eq_normS {α} [CommSemiring α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normS_cert lhs rhs → lhs.denoteS ctx = rhs.denoteS ctx := by
  simp [eq_normS_cert]; intro h
  replace h := congrArg (Poly.denoteS ctx) h
  simp [Expr.denoteS_toPolyS, *] at h
  assumption

noncomputable def eq_normS_nc_cert (lhs rhs : Expr) : Bool :=
  lhs.toPolyS_nc_k.beq' rhs.toPolyS_nc_k

theorem eq_normS_nc {α} [Semiring α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normS_nc_cert lhs rhs → lhs.denoteS ctx = rhs.denoteS ctx := by
  simp [eq_normS_nc_cert]; intro h
  replace h := congrArg (Poly.denoteS ctx) h
  simp [Expr.denoteS_toPolyS_nc, *] at h
  assumption

/-!
Certificates that check the normal form of a commutative semiring term by definitional equality,
as `Expr.eq_of_toPoly_eq_toExpr` does for rings: the kernel computes the polynomial of the term
once and renders it with `Poly.toExpr_k`, instead of normalizing both sides.
-/

theorem Expr.denoteS_num_of_nonneg {α} [Semiring α] (ctx : Context α) (k : Int) (h : k ≥ 0) :
    (Expr.num k).denoteS ctx = denoteSInt k := by
  simp [Expr.denoteS, denoteSInt, Int.not_lt.mpr h]

theorem Power.denoteS_toExpr {α} [Semiring α] (ctx : Context α) (pw : Power) :
    pw.toExpr.denoteS ctx = pw.denote ctx := by
  rw [Power.denote_eq]; unfold Power.toExpr; split
  · next h => simp at h; simp [Expr.denoteS, h, pow_one]
  · simp [Expr.denoteS]

theorem Mon.denoteS_toExpr_go {α} [Semiring α] (ctx : Context α) (m : Mon) (acc : Expr) :
    (Mon.toExpr.go m acc).denoteS ctx = acc.denoteS ctx * m.denote ctx := by
  induction m generalizing acc with
  | unit => simp [Mon.toExpr.go, Mon.denote, mul_one]
  | mult pw m ih =>
    simp only [Mon.toExpr.go, ih]
    show acc.denoteS ctx * pw.toExpr.denoteS ctx * m.denote ctx = _
    rw [Power.denoteS_toExpr, mul_assoc]; rfl

theorem Mon.denoteS_toExpr {α} [Semiring α] (ctx : Context α) (m : Mon) : m.toExpr.denoteS ctx = m.denote ctx := by
  cases m with
  | unit => simp [Mon.toExpr, Expr.denoteS, Mon.denote]
  | mult pw m => simp only [Mon.toExpr, Mon.denoteS_toExpr_go, Power.denoteS_toExpr]; rfl

theorem Poly.denoteS_toExpr_goTerm {α} [Semiring α] (ctx : Context α) (k : Int) (m : Mon) (h : k ≥ 0) :
    (Poly.toExpr.goTerm k m).denoteS ctx = denoteSInt k * m.denote ctx := by
  unfold toExpr.goTerm; split
  · next h' =>
    simp at h'; subst h'
    rw [Mon.denoteS_toExpr, denoteSInt_eq]; simp [natCast_one, one_mul]
  · show (Expr.num k).denoteS ctx * m.toExpr.denoteS ctx = _
    rw [Expr.denoteS_num_of_nonneg ctx k h, Mon.denoteS_toExpr]

theorem Poly.denoteS_toExpr_go {α} [Semiring α] (ctx : Context α) (p : Poly) (acc : Expr) (h : p.NonnegCoeffs) :
    (Poly.toExpr.go p acc).denoteS ctx = acc.denoteS ctx + p.denoteS ctx := by
  induction p generalizing acc with
  | num k =>
    cases h; rename_i hk
    cases hk0 : k == 0
    · simp only [toExpr.go, hk0, Bool.cond_false]
      show acc.denoteS ctx + (Expr.num k).denoteS ctx = _
      rw [Expr.denoteS_num_of_nonneg ctx k hk]; rfl
    · have : k = 0 := by simpa using hk0
      subst this; simp [toExpr.go, Poly.denoteS, denoteSInt, add_zero]
  | add k m p ih =>
    cases h; rename_i hk hp
    simp only [toExpr.go]
    rw [ih _ hp]
    show acc.denoteS ctx + (toExpr.goTerm k m).denoteS ctx + p.denoteS ctx = _
    rw [Poly.denoteS_toExpr_goTerm ctx k m hk, add_assoc]; rfl

theorem Poly.denoteS_toExpr {α} [Semiring α] (ctx : Context α) (p : Poly) (h : p.NonnegCoeffs) :
    p.toExpr.denoteS ctx = p.denoteS ctx := by
  cases p with
  | num k => cases h; rename_i hk; exact Expr.denoteS_num_of_nonneg ctx k hk
  | add k m p =>
    cases h; rename_i hk hp
    simp only [toExpr]
    rw [Poly.denoteS_toExpr_go ctx p _ hp, Poly.denoteS_toExpr_goTerm ctx k m hk]; rfl

noncomputable def Poly.nonneg_k (p : Poly) : Bool :=
  Poly.rec (fun k => Bool.rec true false (Int.blt' k (Int.ofNat 0)))
    (fun k _ _ ih => Bool.rec ih false (Int.blt' k (Int.ofNat 0))) p

theorem Poly.nonnegCoeffs_of_nonneg_k {p : Poly} (h : p.nonneg_k = true) : p.NonnegCoeffs := by
  induction p with
  | num k =>
    have h' : Bool.rec (motive := fun _ => Bool) true false (Int.blt' k (Int.ofNat 0)) = true := h
    cases hk : Int.blt' k (Int.ofNat 0)
    · constructor; have := (Int.blt'_eq_false k 0).mp hk; omega
    · rw [hk] at h'; cases h'
  | add k m p ih =>
    have h' : Bool.rec (motive := fun _ => Bool) p.nonneg_k false (Int.blt' k (Int.ofNat 0)) = true := h
    cases hk : Int.blt' k (Int.ofNat 0)
    · rw [hk] at h'
      constructor
      · have := (Int.blt'_eq_false k 0).mp hk; omega
      · exact ih h'
    · rw [hk] at h'; cases h'

/-!
Balanced polynomial normalization for commutative semiring certificates, like `Expr.toPolyB_k`
for rings.
-/

/-- The polynomial of `a ^ k` in a semiring, where `p` is the polynomial of `a`. -/
noncomputable def Expr.powLeafSB_k (a : Expr) (k : Nat) (p : Poly) : Poly :=
  Bool.rec
    (Expr.rec (fun n => .num (Int.ofNat (Nat.pow (Int.natAbs_k n) k)))
      (fun _ => p.powB_k k) (fun _ => p.powB_k k)
      (fun x => .ofMon (.mult {x, k} .unit)) (fun _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ _ => p.powB_k k)
      (fun _ _ _ => p.powB_k k)
      a)
    (.num 1)
    (k.beq 0)

/-- `e.sumsSB_k acc` prepends to `acc` the polynomials of the summands of `e` in a semiring. -/
noncomputable def Expr.sumsSB_k (e : Expr) : List Poly → List Poly :=
  Expr.rec
    (fun n acc => .num (Int.ofNat (Int.natAbs_k n)) :: acc)
    (fun n acc => .num (Int.ofNat n) :: acc)
    (fun _ acc => .num 0 :: acc)
    (fun x acc => Poly.ofVar x :: acc)
    (fun _ _ acc => .num 0 :: acc)
    (fun _ _ ih₁ ih₂ acc => ih₁ (ih₂ acc))
    (fun _ _ _ _ acc => .num 0 :: acc)
    (fun _ _ ih₁ ih₂ acc => (Poly.sumB_k Poly.combine_k (ih₁ [])).mulB_k (Poly.sumB_k Poly.combine_k (ih₂ [])) :: acc)
    (fun a k ih acc => a.powLeafSB_k k (Poly.sumB_k Poly.combine_k (ih [])) :: acc)
    e

noncomputable def Expr.toPolySB_k (e : Expr) : Poly :=
  Poly.sumB_k Poly.combine_k (e.sumsSB_k [])

/-- `Expr.toPolySB_k` if `bal`, and `Expr.toPolyS_k` otherwise. -/
noncomputable def Expr.toPolySX_k (bal : Bool) (e : Expr) : Poly :=
  Bool.rec e.toPolyS_k e.toPolySB_k bal

/-- Every polynomial of `ps` has nonnegative coefficients. -/
def Poly.NonnegList : List Poly → Prop
  | [] => True
  | p :: ps => p.NonnegCoeffs ∧ NonnegList ps

/-- The sum of the semiring denotations of `ps`. -/
def Poly.denoteSList {α} [Semiring α] (ctx : Context α) : List Poly → α
  | [] => 0
  | p :: ps => p.denoteS ctx + denoteSList ctx ps

section
variable {α} [CommSemiring α] (ctx : Context α)

theorem Poly.combine_k_nonneg {a b : Poly} (ha : a.NonnegCoeffs) (hb : b.NonnegCoeffs) :
    (combine_k a b).NonnegCoeffs ∧ (combine_k a b).denoteS ctx = a.denoteS ctx + b.denoteS ctx := by
  rw [combine_k_eq_combine]; exact ⟨combine_NonnegCoeffs ha hb, denoteS_combine ctx a b ha hb⟩

theorem Poly.pairs_k_nonneg (ps : List Poly) (pend : Option Poly) (hps : NonnegList ps)
    (hpend : ∀ p, pend = some p → p.NonnegCoeffs) :
    NonnegList (pairs_k combine_k ps pend) ∧
      denoteSList ctx (pairs_k combine_k ps pend) = (Option.rec 0 (fun p => p.denoteS ctx) pend : α) + denoteSList ctx ps := by
  induction ps generalizing pend with
  | nil =>
    cases pend with
    | none => exact ⟨trivial, by simp [pairs_k, denoteSList]⟩
    | some p => exact ⟨⟨hpend p rfl, trivial⟩, by simp [pairs_k, denoteSList]⟩
  | cons a ps ih =>
    cases pend with
    | none =>
      have := ih (some a) hps.2 (fun p h => by cases h; exact hps.1)
      exact ⟨this.1, by rw [show pairs_k combine_k (a :: ps) none = pairs_k combine_k ps (some a) from rfl, this.2]; simp [denoteSList]⟩
    | some p =>
      have hc := combine_k_nonneg ctx (hpend p rfl) hps.1
      have := ih none hps.2 (fun _ h => by cases h)
      refine ⟨⟨hc.1, this.1⟩, ?_⟩
      show (combine_k p a).denoteS ctx + denoteSList ctx (pairs_k combine_k ps none) = _
      rw [hc.2, this.2]; simp [denoteSList, Semiring.add_assoc]

theorem Poly.foldr_k_nonneg (ps : List Poly) (hps : NonnegList ps) :
    (foldr_k combine_k ps).NonnegCoeffs ∧ (foldr_k combine_k ps).denoteS ctx = denoteSList ctx ps := by
  induction ps with
  | nil => exact ⟨.num 0 (by decide), by simp [foldr_k, denoteS, denoteSList]⟩
  | cons a ps ih =>
    have := ih hps.2
    have hc := combine_k_nonneg ctx hps.1 this.1
    exact ⟨hc.1, by rw [show foldr_k combine_k (a :: ps) = combine_k a (foldr_k combine_k ps) from rfl, hc.2, this.2]; rfl⟩

theorem Poly.sumGo_k_nonneg (fuel ps : List Poly) (hps : NonnegList ps) :
    (sumGo_k combine_k fuel ps).NonnegCoeffs ∧ (sumGo_k combine_k fuel ps).denoteS ctx = denoteSList ctx ps := by
  induction fuel generalizing ps with
  | nil => exact foldr_k_nonneg ctx ps hps
  | cons _ fuel ih =>
    match ps, hps with
    | [], _ => exact ⟨.num 0 (by decide), by simp [sumGo_k, denoteS, denoteSList]⟩
    | [a], hps => exact ⟨hps.1, by simp [sumGo_k, denoteSList]⟩
    | a :: b :: ps, hps =>
      have hp := pairs_k_nonneg ctx (a :: b :: ps) none hps (fun _ h => by cases h)
      have := ih _ hp.1
      exact ⟨this.1, by
        rw [show sumGo_k combine_k (_ :: fuel) (a :: b :: ps) = sumGo_k combine_k fuel (pairs_k combine_k (a :: b :: ps) none) from rfl,
          this.2, hp.2]; simp⟩

theorem Poly.sumB_k_nonneg (ps : List Poly) (hps : NonnegList ps) :
    (sumB_k combine_k ps).NonnegCoeffs ∧ (sumB_k combine_k ps).denoteS ctx = denoteSList ctx ps :=
  sumGo_k_nonneg ctx ps ps hps

theorem Poly.mulTerms_k_nonneg (p₁ p₂ : Poly) (h₁ : p₁.NonnegCoeffs) (h₂ : p₂.NonnegCoeffs) :
    NonnegList (mulTerms_k p₁ p₂) ∧ denoteSList ctx (mulTerms_k p₁ p₂) = p₁.denoteS ctx * p₂.denoteS ctx := by
  induction p₁ with
  | num k =>
    cases h₁; rename_i hk
    refine ⟨⟨by rw [mulConst_k_eq_mulConst]; exact mulConst_NonnegCoeffs hk h₂, trivial⟩, ?_⟩
    show (p₂.mulConst_k k).denoteS ctx + 0 = _
    rw [mulConst_k_eq_mulConst, denoteS_mulConst ctx k p₂ hk h₂]; simp [denoteS]
  | add k m p ih =>
    cases h₁; rename_i hk hp
    have := ih hp
    refine ⟨⟨by rw [mulMon_k_eq_mulMon]; exact mulMon_NonnegCoeffs m hk h₂, this.1⟩, ?_⟩
    show (p₂.mulMon_k k m).denoteS ctx + denoteSList ctx (mulTerms_k p p₂) = _
    rw [this.2, mulMon_k_eq_mulMon, denoteS_mulMon ctx k m p₂ hk h₂]; simp [denoteS, Semiring.right_distrib]

theorem Poly.mulB_k_nonneg {p₁ p₂ : Poly} (h₁ : p₁.NonnegCoeffs) (h₂ : p₂.NonnegCoeffs) :
    (mulB_k p₁ p₂).NonnegCoeffs ∧ (mulB_k p₁ p₂).denoteS ctx = p₁.denoteS ctx * p₂.denoteS ctx := by
  have ht := mulTerms_k_nonneg ctx p₁ p₂ h₁ h₂
  have := sumB_k_nonneg ctx _ ht.1
  cases p₁ with
  | num k =>
    cases h₁; rename_i hk
    refine ⟨by show (p₂.mulConst_k k).NonnegCoeffs; rw [mulConst_k_eq_mulConst]; exact mulConst_NonnegCoeffs hk h₂, ?_⟩
    show (p₂.mulConst_k k).denoteS ctx = _
    rw [mulConst_k_eq_mulConst, denoteS_mulConst ctx k p₂ hk h₂]; simp [denoteS]
  | add k₁ m₁ q₁ =>
    cases p₂ with
    | num k =>
      cases h₂; rename_i hk
      refine ⟨by show ((Poly.add k₁ m₁ q₁).mulConst_k k).NonnegCoeffs; rw [mulConst_k_eq_mulConst]; exact mulConst_NonnegCoeffs hk h₁, ?_⟩
      show ((Poly.add k₁ m₁ q₁).mulConst_k k).denoteS ctx = _
      rw [mulConst_k_eq_mulConst, denoteS_mulConst ctx k _ hk h₁, CommSemiring.mul_comm]; simp [denoteS]
    | add k₂ m₂ q₂ =>
      have hmon {p q : Poly} (hp : p.NonnegCoeffs) (hq : q.NonnegCoeffs) (h : p.isMon_k = true) :
          (p.mulByMon_k q).NonnegCoeffs ∧ (p.mulByMon_k q).denoteS ctx = p.denoteS ctx * q.denoteS ctx := by
        have ⟨k, m, hpm⟩ := eq_of_isMon_k h; subst hpm
        cases hp; rename_i hk _
        refine ⟨by show (q.mulMon_k k m).NonnegCoeffs; rw [mulMon_k_eq_mulMon]; exact mulMon_NonnegCoeffs m hk hq, ?_⟩
        show (q.mulMon_k k m).denoteS ctx = _
        rw [mulMon_k_eq_mulMon, denoteS_mulMon ctx k m q hk hq]; simp [denoteS]
      show (Bool.rec (Bool.rec _ _ (Poly.add k₂ m₂ q₂).isMon_k) _ (Poly.add k₁ m₁ q₁).isMon_k : Poly).NonnegCoeffs ∧
        (Bool.rec (Bool.rec _ _ (Poly.add k₂ m₂ q₂).isMon_k) _ (Poly.add k₁ m₁ q₁).isMon_k : Poly).denoteS ctx = _
      cases hm₁ : (Poly.add k₁ m₁ q₁).isMon_k
      · cases hm₂ : (Poly.add k₂ m₂ q₂).isMon_k
        · exact ⟨this.1, by rw [show sumB_k combine_k _ = sumB_k combine_k _ from rfl, this.2, ht.2]⟩
        · have := hmon h₂ h₁ hm₂
          exact ⟨this.1, by rw [this.2, CommSemiring.mul_comm]⟩
      · exact hmon h₁ h₂ hm₁

theorem Poly.powB_k_nonneg {p : Poly} (k : Nat) (h : p.NonnegCoeffs) :
    (powB_k p k).NonnegCoeffs ∧ (powB_k p k).denoteS ctx = p.denoteS ctx ^ k := by
  induction k with
  | zero => exact ⟨.num 1 (by decide), by simp [powB_k, denoteS, Semiring.pow_zero]⟩
  | succ k ih =>
    cases k with
    | zero => exact ⟨h, by simp [powB_k, Semiring.pow_succ, Semiring.pow_zero]⟩
    | succ k =>
      have hm := mulB_k_nonneg ctx h ih.1
      exact ⟨hm.1, by
        rw [show powB_k p (k + 2) = p.mulB_k (powB_k p (k + 1)) from rfl, hm.2, ih.2,
          Semiring.pow_succ (n := k + 1), CommSemiring.mul_comm]⟩

theorem Expr.powLeafSB_k_nonneg (a : Expr) (k : Nat) {p : Poly} (hp : p.NonnegCoeffs) (h : p.denoteS ctx = a.denoteS ctx) :
    (a.powLeafSB_k k p).NonnegCoeffs ∧ (a.powLeafSB_k k p).denoteS ctx = a.denoteS ctx ^ k := by
  unfold powLeafSB_k
  cases hk : k.beq 0
  · have hk : k ≠ 0 := Nat.ne_of_beq_eq_false hk
    dsimp only
    have hpow := Poly.powB_k_nonneg ctx k hp
    cases a with
    | num n =>
      refine ⟨.num _ (Int.natCast_nonneg _), ?_⟩
      show denoteSInt (Int.ofNat (Nat.pow (Int.natAbs_k n) k)) = _
      rw [denoteSInt_eq, Int.natAbs_k_eq, denoteS_num, Semiring.ofNat_eq_natCast]
      rw [show (Int.ofNat (Nat.pow n.natAbs k)).toNat = n.natAbs ^ k from rfl, Semiring.natCast_pow]
    | var x =>
      refine ⟨.add _ _ _ (by decide) (.num _ (by decide)), ?_⟩
      simp [Poly.ofMon, Poly.denoteS, Mon.denote, Power.denote_eq, denoteS_var]
    | _ => rw [← h]; exact hpow
  · have hk : k = 0 := Nat.eq_of_beq_eq_true hk
    subst hk; exact ⟨.num 1 (by decide), by simp [Poly.denoteS, Semiring.pow_zero]⟩

theorem Expr.sumsSB_k_nonneg (e : Expr) (acc : List Poly) (hacc : Poly.NonnegList acc) :
    Poly.NonnegList (e.sumsSB_k acc) ∧ Poly.denoteSList ctx (e.sumsSB_k acc) = e.denoteS ctx + Poly.denoteSList ctx acc := by
  have hB (a : Expr) (ih : ∀ acc, Poly.NonnegList acc → Poly.NonnegList (a.sumsSB_k acc) ∧
      Poly.denoteSList ctx (a.sumsSB_k acc) = a.denoteS ctx + Poly.denoteSList ctx acc) :
      (Poly.sumB_k Poly.combine_k (a.sumsSB_k [])).NonnegCoeffs ∧
        (Poly.sumB_k Poly.combine_k (a.sumsSB_k [])).denoteS ctx = a.denoteS ctx := by
    have h := ih [] trivial
    have := Poly.sumB_k_nonneg ctx _ h.1
    exact ⟨this.1, by rw [this.2, h.2]; simp [Poly.denoteSList]⟩
  induction e generalizing acc with
  | num n =>
    refine ⟨⟨.num _ (Int.natCast_nonneg _), hacc⟩, ?_⟩
    show denoteSInt (Int.ofNat (Int.natAbs_k n)) + _ = _
    rw [denoteSInt_eq, Int.natAbs_k_eq, denoteS_num, Semiring.ofNat_eq_natCast]; simp
  | natCast n =>
    refine ⟨⟨.num _ (Int.natCast_nonneg _), hacc⟩, ?_⟩
    show denoteSInt (Int.ofNat n) + _ = _
    rw [denoteSInt_eq, denoteS_natCast, Semiring.ofNat_eq_natCast]; simp
  | intCast n => exact ⟨⟨.num 0 (by decide), hacc⟩, by show denoteSInt 0 + _ = _; simp [denoteS_intCast]⟩
  | var x =>
    refine ⟨⟨by simp [Poly.ofVar, Poly.ofMon]; exact .add _ _ _ (by decide) (.num _ (by decide)), hacc⟩, ?_⟩
    show (Poly.ofVar x).denoteS ctx + _ = _
    rw [Poly.denoteS_ofVar]; rfl
  | neg a _ => exact ⟨⟨.num 0 (by decide), hacc⟩, by show denoteSInt 0 + _ = _; simp [denoteS_neg]⟩
  | add a b iha ihb =>
    have hb := ihb acc hacc
    have ha := iha _ hb.1
    exact ⟨ha.1, by
      rw [show (Expr.add a b).sumsSB_k acc = a.sumsSB_k (b.sumsSB_k acc) from rfl, ha.2, hb.2, denoteS_add, Semiring.add_assoc]⟩
  | sub a b _ _ => exact ⟨⟨.num 0 (by decide), hacc⟩, by show denoteSInt 0 + _ = _; simp [denoteS_sub]⟩
  | mul a b iha ihb =>
    have ha := hB a iha
    have hb := hB b ihb
    have hm := Poly.mulB_k_nonneg ctx ha.1 hb.1
    refine ⟨⟨hm.1, hacc⟩, ?_⟩
    show ((Poly.sumB_k Poly.combine_k (a.sumsSB_k [])).mulB_k (Poly.sumB_k Poly.combine_k (b.sumsSB_k []))).denoteS ctx
      + Poly.denoteSList ctx acc = _
    rw [hm.2, ha.2, hb.2, denoteS_mul]
  | pow a k ih =>
    have ha := hB a ih
    have hp := Expr.powLeafSB_k_nonneg ctx a k ha.1 ha.2
    refine ⟨⟨hp.1, hacc⟩, ?_⟩
    show (a.powLeafSB_k k (Poly.sumB_k Poly.combine_k (a.sumsSB_k []))).denoteS ctx + Poly.denoteSList ctx acc = _
    rw [hp.2, denoteS_pow]

theorem Expr.toPolySX_k_nonneg (bal : Bool) (e : Expr) :
    (e.toPolySX_k bal).NonnegCoeffs ∧ (e.toPolySX_k bal).denoteS ctx = e.denoteS ctx := by
  cases bal
  · show e.toPolyS_k.NonnegCoeffs ∧ e.toPolyS_k.denoteS ctx = _
    rw [toPolyS_k_eq_toPolyS]; exact ⟨toPolyS_NonnegCoeffs, denoteS_toPolyS ctx e⟩
  · have h := e.sumsSB_k_nonneg ctx [] trivial
    have := Poly.sumB_k_nonneg ctx _ h.1
    exact ⟨this.1, by
      show (Poly.sumB_k Poly.combine_k (e.sumsSB_k [])).denoteS ctx = _
      rw [this.2, h.2]; simp [Poly.denoteSList]⟩

end

theorem Expr.eq_of_toPolyS_eq_toExpr {α} [CommSemiring α] (ctx : Context α) (bal : Bool) (a b : Expr) (p : Poly)
    (h₁ : p = a.toPolySX_k bal) (h₂ : b = p.toExpr_k) : a.denoteS ctx = b.denoteS ctx := by
  have h := Expr.toPolySX_k_nonneg ctx bal a
  subst h₁ h₂
  rw [Poly.toExpr_k_eq, Poly.denoteS_toExpr _ _ h.1, h.2]

theorem Expr.eq_of_toPolyS_eq_add_toExpr {α} [CommSemiring α] (ctx : Context α) (bal : Bool) (a b : Expr) (p q r : Poly)
    (h₁ : p = a.toPolySX_k bal) (h₂ : b = .add q.toExpr_k r.toExpr_k) (h₃ : p = q.combine_k r)
    (h₄ : (q.nonneg_k && r.nonneg_k) = true) : a.denoteS ctx = b.denoteS ctx := by
  rw [Bool.and_eq_true] at h₄
  have hq := Poly.nonnegCoeffs_of_nonneg_k h₄.1
  have hr := Poly.nonnegCoeffs_of_nonneg_k h₄.2
  subst h₂
  rw [← (Expr.toPolySX_k_nonneg ctx bal a).2, ← h₁, h₃, Poly.combine_k_eq_combine,
    Poly.denoteS_combine _ _ _ hq hr]
  show _ = q.toExpr_k.denoteS ctx + r.toExpr_k.denoteS ctx
  rw [Poly.toExpr_k_eq, Poly.toExpr_k_eq, Poly.denoteS_toExpr _ _ hq, Poly.denoteS_toExpr _ _ hr]


/-! Relations whose sides have the same polynomial in a commutative semiring. -/

theorem eq_true_of_toPolyS {α} [CommSemiring α] (ctx : Context α) (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolySX_k bal₁) (h₂ : p = rhs.toPolySX_k bal₂) : (lhs.denoteS ctx = rhs.denoteS ctx) = True := by
  have e₁ := (Expr.toPolySX_k_nonneg ctx bal₁ lhs).2
  have e₂ := (Expr.toPolySX_k_nonneg ctx bal₂ rhs).2
  rw [← h₁] at e₁; rw [← h₂] at e₂
  exact eq_true (e₁.symm.trans e₂)

theorem le_true_of_toPolyS {α} [CommSemiring α] [LE α] [Std.IsPreorder α] (ctx : Context α) (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolySX_k bal₁) (h₂ : p = rhs.toPolySX_k bal₂) : (lhs.denoteS ctx ≤ rhs.denoteS ctx) = True := by
  have h := of_eq_true (eq_true_of_toPolyS ctx bal₁ bal₂ lhs rhs p h₁ h₂)
  rw [h]; exact eq_true (Std.le_refl _)

theorem lt_false_of_toPolyS {α} [CommSemiring α] [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] (ctx : Context α)
    (bal₁ bal₂ : Bool) (lhs rhs : Expr) (p : Poly)
    (h₁ : p = lhs.toPolySX_k bal₁) (h₂ : p = rhs.toPolySX_k bal₂) : (lhs.denoteS ctx < rhs.denoteS ctx) = False := by
  have h := of_eq_true (eq_true_of_toPolyS ctx bal₁ bal₂ lhs rhs p h₁ h₂)
  rw [h]; exact eq_false (Std.lt_irrefl)

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
