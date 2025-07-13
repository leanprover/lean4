/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Int.Lemmas
public import Init.Data.Int.DivMod
public import Init.Data.Int.Linear
public import Init.Data.RArray

public section

-- TODO: this namespace will deleted after we move to the new encoding using `Nat.ToInt` namespace.
-- Bootstrapping sucks.
namespace Int.OfNat
/-!
Helper definitions and theorems for converting `Nat` expressions into `Int` one.
We use them to implement the arithmetic theories in `grind`
-/

abbrev Var := Nat
abbrev Context := Lean.RArray Nat
@[expose]
def Var.denote (ctx : Context) (v : Var) : Nat :=
  ctx.get v

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mul  (a b : Expr)
  | div  (a b : Expr)
  | mod  (a b : Expr)
  | pow  (a : Expr) (k : Nat)
  deriving BEq

@[expose]
def Expr.denote (ctx : Context) : Expr → Nat
  | .num k    => k
  | .var v    => v.denote ctx
  | .add a b  => Nat.add (denote ctx a) (denote ctx b)
  | .mul a b  => Nat.mul (denote ctx a) (denote ctx b)
  | .div a b  => Nat.div (denote ctx a) (denote ctx b)
  | .mod a b  => Nat.mod (denote ctx a) (denote ctx b)
  | .pow a k  => Nat.pow (denote ctx a) k

@[expose]
def Expr.denoteAsInt (ctx : Context) : Expr → Int
  | .num k    => Int.ofNat k
  | .var v    => Int.ofNat (v.denote ctx)
  | .add a b  => Int.add (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .mul a b  => Int.mul (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .div a b  => Int.ediv (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .mod a b  => Int.emod (denoteAsInt ctx a) (denoteAsInt ctx b)
  | .pow a k  => Int.pow (denoteAsInt ctx a) k

theorem Expr.denoteAsInt_eq (ctx : Context) (e : Expr) : e.denoteAsInt ctx = e.denote ctx := by
  induction e <;> simp [denote, denoteAsInt, *] <;> rfl

theorem Expr.eq_denoteAsInt (ctx : Context) (e : Expr) : e.denote ctx = e.denoteAsInt ctx := by
  apply Eq.symm; apply denoteAsInt_eq

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

namespace Nat.ToInt

theorem ofNat_toNat (a : Int) : (NatCast.natCast a.toNat : Int) = if a ≤ 0 then 0 else a := by
  simp [Int.max_def]

theorem toNat_nonneg (x : Nat) : (-1:Int) * (NatCast.natCast x) ≤ 0 := by
  simp

theorem natCast_ofNat (n : Nat) : (NatCast.natCast (OfNat.ofNat n : Nat) : Int) = OfNat.ofNat n := by
  rfl

theorem of_eq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a = b → a' = b' := by
  intro h; replace h := congrArg (NatCast.natCast (R := Int)) h
  rw [h₁, h₂] at h; assumption

theorem of_diseq {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a ≠ b → a' ≠ b' := by
  intro hne h; rw [← h₁, ← h₂] at h
  replace h := Int.ofNat_inj.mp h; contradiction

theorem of_dvd (d a : Nat) (d' a' : Int)
    (h₁ : NatCast.natCast d = d') (h₂ : NatCast.natCast a = a') : d ∣ a → d' ∣ a' := by
  simp [← h₁, ←h₂, Int.ofNat_dvd]

theorem of_le {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : a ≤ b → a' ≤ b' := by
  intro h; replace h := Int.ofNat_le |>.mpr h
  rw [← h₁, ← h₂]; assumption

theorem of_not_le {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : ¬ (a ≤ b) → b' + 1 ≤ a' := by
  intro h; rw [← Int.ofNat_le] at h
  rw [← h₁, ← h₂]; show (↑b + 1 : Int) ≤ a; omega

theorem add_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a + b) = a' + b' := by
  simp_all [Int.natCast_add]

theorem mul_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a * b) = a' * b' := by
  simp_all [Int.natCast_mul]

theorem sub_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a - b) = if b' + (-1)*a' ≤ 0 then a' - b' else 0 := by
  rw [Int.neg_mul, ← Int.sub_eq_add_neg, Int.one_mul]
  split
  next h =>
    have h := Int.le_of_sub_nonpos h
    simp [← h₁, ← h₂, Int.ofNat_le] at h
    simp [Int.ofNat_sub h]
    rw [← h₁, ← h₂]
  next h =>
    have : ¬ (↑b : Int) ≤ ↑a := by
      intro h
      replace h := Int.sub_nonpos_of_le h
      simp [h₁, h₂] at h
      contradiction
    rw [Int.ofNat_le] at this
    simp [Lean.Omega.Int.ofNat_sub_eq_zero this]

theorem pow_congr {a : Nat} (k : Nat) (a' : Int)
    (h₁ : NatCast.natCast a = a') : NatCast.natCast (a ^ k) = a' ^ k := by
  simp_all [Int.natCast_pow]

theorem div_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a / b) = a' / b' := by
  simp_all [Int.natCast_ediv]

theorem mod_congr {a b : Nat} {a' b' : Int}
    (h₁ : NatCast.natCast a = a') (h₂ : NatCast.natCast b = b') : NatCast.natCast (a % b) = a' % b' := by
  simp_all [Int.natCast_emod]

end Nat.ToInt

namespace Int.Nonneg


@[expose]
def num_cert (a : Int) : Bool := a ≥ 0

theorem num (a : Int) : num_cert a → a ≥ 0 := by
  simp [num_cert]

theorem add (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a + b ≥ 0 := by
  exact Int.add_nonneg h₁ h₂

theorem mul (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a * b ≥ 0 := by
  exact Int.mul_nonneg h₁ h₂

theorem div (a b : Int) (h₁ : a ≥ 0) (h₂ : b ≥ 0) : a / b ≥ 0 := by
  exact Int.ediv_nonneg h₁ h₂

theorem pow (a : Int) (k : Nat) (h₁ : a ≥ 0) : a ^ k ≥ 0 := by
  exact Int.pow_nonneg h₁

theorem mod (a b : Int) (h₁ : a ≥ 0) : a % b ≥ 0 := by
  by_cases b = 0
  next => simp [*]
  next h => exact emod_nonneg a h

theorem natCast (a : Nat) : (NatCast.natCast a : Int) ≥ 0 := by
  simp

theorem toPoly (e : Int) : e ≥ 0 → -1 * e ≤ 0 := by
  omega

end Int.Nonneg
