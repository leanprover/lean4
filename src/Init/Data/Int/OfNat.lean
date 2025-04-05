/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Int.Lemmas
import Init.Data.Int.DivMod
import Init.Data.RArray

namespace Int.OfNat
/-!
Helper definitions and theorems for converting `Nat` expressions into `Int` one.
We use them to implement the arithmetic theories in `grind`
-/

abbrev Var := Nat
abbrev Context := Lean.RArray Nat
def Var.denote (ctx : Context) (v : Var) : Nat :=
  ctx.get v

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mul  (a b : Expr)
  | div  (a b : Expr)
  | mod  (a b : Expr)
  deriving BEq

def Expr.denote (ctx : Context) : Expr → Nat
  | .num k    => k
  | .var v    => v.denote ctx
  | .add a b  => Nat.add (denote ctx a) (denote ctx b)
  | .mul a b  => Nat.mul (denote ctx a) (denote ctx b)
  | .div a b  => Nat.div (denote ctx a) (denote ctx b)
  | .mod a b  => Nat.mod (denote ctx a) (denote ctx b)

def Expr.denoteAsInt (ctx : Context) : Expr → Int
  | .num k    => Int.ofNat k
  | .var v    => Int.ofNat (v.denote ctx)
  | .add a b  => Int.add (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .mul a b  => Int.mul (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .div a b  => Int.ediv (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .mod a b  => Int.emod (denoteAsInt ctx a) (denoteAsInt ctx b)

theorem Expr.denoteAsInt_eq (ctx : Context) (e : Expr) : e.denoteAsInt ctx = e.denote ctx := by
  induction e <;> simp [denote, denoteAsInt, Int.ofNat_ediv, *] <;> rfl

theorem Expr.eq (ctx : Context) (lhs rhs : Expr)
    : (lhs.denote ctx = rhs.denote ctx) = (lhs.denoteAsInt ctx = rhs.denoteAsInt ctx) := by
  simp [denoteAsInt_eq, Int.ofNat_inj]

theorem Expr.le (ctx : Context) (lhs rhs : Expr)
    : (lhs.denote ctx ≤ rhs.denote ctx) = (lhs.denoteAsInt ctx ≤ rhs.denoteAsInt ctx) := by
  simp [denoteAsInt_eq, Int.ofNat_le]

theorem of_le (ctx : Context) (lhs rhs : Expr)
    : lhs.denote ctx ≤ rhs.denote ctx → lhs.denoteAsInt ctx ≤ rhs.denoteAsInt ctx := by
  rw [Expr.le ctx lhs rhs]; simp

theorem of_not_le (ctx : Context) (lhs rhs : Expr)
    : ¬ lhs.denote ctx ≤ rhs.denote ctx → ¬ lhs.denoteAsInt ctx ≤ rhs.denoteAsInt ctx := by
  rw [Expr.le ctx lhs rhs]; simp

theorem of_dvd (ctx : Context) (d : Nat) (e : Expr)
    : d ∣ e.denote ctx → Int.ofNat d ∣ e.denoteAsInt ctx := by
  simp [Expr.denoteAsInt_eq, Int.ofNat_dvd]

theorem of_eq (ctx : Context) (lhs rhs : Expr)
    : lhs.denote ctx = rhs.denote ctx → lhs.denoteAsInt ctx = rhs.denoteAsInt ctx := by
  rw [Expr.eq ctx lhs rhs]; simp

theorem of_not_eq (ctx : Context) (lhs rhs : Expr)
    : ¬ lhs.denote ctx = rhs.denote ctx → ¬ lhs.denoteAsInt ctx = rhs.denoteAsInt ctx := by
  rw [Expr.eq ctx lhs rhs]; simp

theorem ofNat_toNat (a : Int) : (NatCast.natCast a.toNat : Int) = if a ≤ 0 then 0 else a := by
  split
  next h =>
    rw [Int.toNat_of_nonpos h]; rfl
  next h =>
    simp at h
    have := Int.toNat_of_nonneg (Int.le_of_lt h)
    assumption

theorem Expr.denoteAsInt_nonneg (ctx : Context) (e : Expr) : 0 ≤ e.denoteAsInt ctx := by
  simp [Expr.denoteAsInt_eq]

end Int.OfNat
