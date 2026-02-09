/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Linarith
import Init.Data.AC
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.LemmasAux
import Init.Omega
@[expose] public section
namespace Lean.Grind.Linarith
open Std

def Expr.denoteN {α} [NatModule α] (ctx : Context α) : Expr → α
  | .sub .. | .neg .. | .intMul ..
  | zero      => 0
  | .var v    => v.denote ctx
  | .add a b  => denoteN ctx a + denoteN ctx b
  | .natMul k a  => k • denoteN ctx a

inductive Poly.NonnegCoeffs : Poly → Prop
  | nil : NonnegCoeffs .nil
  | add (a : Int) (x : Var) (p : Poly) : a ≥ 0 → NonnegCoeffs p → NonnegCoeffs (.add a x p)

def Poly.denoteN {α} [NatModule α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .nil => 0
  | .add k v p =>
    bif k < 0 then
      0
    else
      k.natAbs • v.denote ctx + denoteN ctx p

def Poly.denoteN_nil {α} [NatModule α] (ctx : Context α) : Poly.denoteN ctx .nil = 0 := rfl

def Poly.denoteN_add {α} [NatModule α] (ctx : Context α) (k : Int) (x : Var) (p : Poly)
    : k ≥ 0 → Poly.denoteN ctx (.add k x p) = k.toNat • x.denote ctx + p.denoteN ctx := by
  intro h; simp [denoteN, cond_eq_ite]; split
  next => omega
  next =>
    have : (k.natAbs : Int) = k.toNat := by
      rw [Int.toNat_of_nonneg h, Int.natAbs_of_nonneg h]
    rw [Int.ofNat_inj.mp this]

attribute [local simp] Poly.denoteN_nil Poly.denoteN_add
open AddCommMonoid AddCommGroup NatModule IntModule

-- Helper instance for `ac_rfl`
local instance {α} [NatModule α] : Std.Associative (· + · : α → α → α) where
  assoc := AddCommMonoid.add_assoc
-- Helper instance for `ac_rfl`
local instance {α} [NatModule α] : Std.Commutative (· + · : α → α → α) where
  comm := AddCommMonoid.add_comm

theorem Poly.denoteN_insert {α} [NatModule α] (ctx : Context α) (k : Int) (x : Var) (p : Poly)
    : k ≥ 0 → p.NonnegCoeffs → (insert k x p).denoteN ctx = k.toNat • x.denote ctx + p.denoteN ctx := by
  fun_induction insert
  next => intros; simp [*]
  next => intro h₁ h₂; cases h₂; simp [*]
  next h₁ h₂ h₃ =>
    intro h₄ h₅; cases h₅; simp [*]
    simp at h₃; simp at h₂; subst h₂
    rw [← add_assoc, ← add_nsmul, ← Int.toNat_add, h₃, Int.toNat_zero, zero_nsmul, zero_add] <;> assumption
  next h _ =>
    intro h₁ h₂; cases h₂; rw [denoteN_add] <;> simp <;> try omega
    next h₂ _ =>
    simp at h; subst h;
    rw [Int.toNat_add h₁ h₂, add_nsmul]; simp [*]; ac_rfl
  next ih =>
    intro h₁ h₂; cases h₂; simp [*]; ac_rfl

attribute [local simp] Poly.denoteN_insert

theorem Poly.denoteN_append {α} [NatModule α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (append p₁ p₂).denoteN ctx = p₁.denoteN ctx + p₂.denoteN ctx := by
  fun_induction append <;> intro h₁ h₂; simp [*]
  next => rw [zero_add]
  next ih => cases h₁; next hn₁ hn₂ => simp [ih hn₂ h₂, *]; ac_rfl

attribute [local simp] Poly.denoteN_append

theorem Poly.denoteN_combine {α} [NatModule α] (ctx : Context α) (p₁ p₂ : Poly)
    : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.combine p₂).denoteN ctx = p₁.denoteN ctx + p₂.denoteN ctx := by
  fun_induction p₁.combine p₂ <;> intro h₁ h₂ <;> try simp [*, zero_add, add_zero]
  next hx _ h ih =>
    simp at hx
    simp +zetaDelta at h
    cases h₁; cases h₂
    next h₁ _ h₂ =>
    simp [ih h₁ h₂, *]
    rw [add_left_comm, add_assoc, ← add_assoc, ← add_nsmul, ← Int.toNat_add, Int.add_comm, h,
      Int.toNat_zero, zero_nsmul, zero_add] <;> assumption
  next hx _ h ih =>
    simp at hx
    cases h₁; cases h₂
    next hp₁ h₁ hp₂ h₂ =>
    simp +zetaDelta [*]
    rw [denoteN_add, ih h₁ h₂, Int.toNat_add hp₁ hp₂, add_nsmul]; ac_rfl; omega
  next ih =>
    cases h₁; next h₁ =>
    simp [ih h₁ h₂, *]; ac_rfl
  next ih =>
    cases h₂; next h₂ =>
    simp [ih h₁ h₂, *]; ac_rfl

theorem Poly.denoteN_mul' {α} [NatModule α] (ctx : Context α) (p : Poly) (k : Nat) : p.NonnegCoeffs → (p.mul' k).denoteN ctx = k • p.denoteN ctx := by
  induction p <;> simp [mul', *, nsmul_zero]
  next ih =>
    intro h; cases h; next hp h =>
    have hk : (k : Int) ≥ 0 := by simp
    simp [*]
    rw [denoteN_add, Int.toNat_mul, mul_nsmul, Int.toNat_natCast, nsmul_add, ih h]
    assumption; assumption;
    exact Int.mul_nonneg hk hp

theorem Poly.denoteN_mul {α} [NatModule α] (ctx : Context α) (p : Poly) (k : Nat) : p.NonnegCoeffs → (p.mul k).denoteN ctx = k • p.denoteN ctx := by
  simp [mul]; intro h
  split
  next => simp [*, zero_nsmul]
  next => simp [denoteN_mul', *]

def Expr.toPolyN : Expr → Poly
  | .sub .. | .neg .. | .intMul ..
  | zero        => .nil
  | .var v      => .add 1 v .nil
  | .add a b    => a.toPolyN.combine b.toPolyN
  | .natMul k a => a.toPolyN.mul k

theorem Poly.mul'_Nonneg (p : Poly) (k : Nat) : p.NonnegCoeffs → (p.mul' k).NonnegCoeffs := by
  induction p
  next => intro; simp [mul']; assumption
  next ih =>
    have hk : (k : Int) ≥ 0 := by simp
    intro h; cases h; next hp h =>
    simp [mul']
    constructor
    next => exact Int.mul_nonneg hk hp
    next => exact ih h

theorem Poly.mul_Nonneg (p : Poly) (k : Nat) : p.NonnegCoeffs → (p.mul k).NonnegCoeffs := by
  simp [mul]; intro h
  split
  next => constructor
  next => simp [Poly.mul'_Nonneg, *]

theorem Poly.append_Nonneg (p₁ p₂ : Poly) : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.append p₂).NonnegCoeffs := by
  fun_induction append <;> intro h₁ h₂; simp [*]
  next ih => cases h₁; constructor; assumption; apply ih <;> assumption

theorem Poly.combine_Nonneg (p₁ p₂ : Poly) : p₁.NonnegCoeffs → p₂.NonnegCoeffs → (p₁.combine p₂).NonnegCoeffs := by
  fun_induction Poly.combine
  next => intros; assumption
  next => intros; assumption
  next ih =>
    intro h₁ h₂; cases h₁; cases h₂
    apply ih <;> assumption
  next h ih =>
    intro h₁ h₂; cases h₁; cases h₂
    constructor; simp +zetaDelta; omega
    apply ih <;> assumption
  next ih =>
    intro h₁ h₂; cases h₁; cases h₂
    constructor; simp +zetaDelta; omega
    apply ih; assumption; constructor; assumption; assumption
  next ih =>
    intro h₁ h₂; cases h₁; cases h₂
    constructor; assumption
    apply ih; constructor; assumption; assumption; assumption

theorem Expr.toPolyN_Nonneg (e : Expr) : e.toPolyN.NonnegCoeffs := by
  fun_induction toPolyN <;> try constructor <;> simp
  next => constructor; simp; constructor
  next => apply Poly.combine_Nonneg <;> assumption
  next => apply Poly.mul_Nonneg; assumption

theorem Expr.denoteN_toPolyN {α} [NatModule α] (ctx : Context α) (e : Expr) : e.toPolyN.denoteN ctx = e.denoteN ctx := by
  fun_induction toPolyN <;> simp [denoteN, add_zero, one_nsmul]
  next => rw [Poly.denoteN_combine]; simp [*]; apply toPolyN_Nonneg; apply toPolyN_Nonneg
  next => rw [Poly.denoteN_mul]; simp [*]; apply toPolyN_Nonneg

def eq_normN_cert (lhs rhs : Expr) : Bool :=
  lhs.toPolyN == rhs.toPolyN

theorem eq_normN {α} [NatModule α] (ctx : Context α) (lhs rhs : Expr)
    : eq_normN_cert lhs rhs → lhs.denoteN ctx = rhs.denoteN ctx := by
  simp [eq_normN_cert]; intro h
  replace h := congrArg (Poly.denoteN ctx) h
  simp [Expr.denoteN_toPolyN, *] at h
  assumption

end Lean.Grind.Linarith
