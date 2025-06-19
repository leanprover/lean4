/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Grind.Ring.Envelope
import Init.Data.Hashable
import Init.Data.RArray

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

end Lean.Grind.Ring.OfSemiring
