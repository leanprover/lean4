/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.Ord
import Init.Grind.CommRing.Basic

namespace Lean.Grind
namespace CommRing

abbrev Var := Nat

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | neg (a : Expr)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | mul (a b : Expr)
  | pow (a : Expr) (k : Nat)
  deriving Inhabited, BEq

-- TODO: add support for universes to Lean.RArray
inductive RArray (α : Type u) : Type u where
  | leaf : α → RArray α
  | branch : Nat → RArray α → RArray α → RArray α

def RArray.get (a : RArray α) (n : Nat) : α :=
  match a with
  | .leaf x => x
  | .branch p l r => if n < p then l.get n else r.get n

abbrev Context (α : Type u) := RArray α

def Var.denote (ctx : Context α) (v : Var) : α :=
  ctx.get v

def Expr.denote [CommRing α] (ctx : Context α) : Expr → α
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .mul a b  => denote ctx a * denote ctx b
  | .neg a    => -denote ctx a
  | .num k    => k
  | .var v    => v.denote ctx
  | .pow a k  => denote ctx a ^ k

structure Power where
  x : Var
  k : Nat
  deriving BEq

def Power.varLt (p₁ p₂ : Power) : Bool :=
  p₁.x.blt p₂.x

def Power.denote [CommRing α] (ctx : Context α) : Power → α
  | {x, k} =>
    match k with
    | 0 => 1
    | 1 => x.denote ctx
    | k => x.denote ctx ^ k

inductive Mon where
  | leaf (p : Power)
  | cons (p : Power) (m : Mon)
  deriving BEq

def Mon.denote [CommRing α] (ctx : Context α) : Mon → α
  | .leaf p => p.denote ctx
  | .cons p m => p.denote ctx * denote ctx m

def Mon.denote' [CommRing α] (ctx : Context α) : Mon → α
  | .leaf p => p.denote ctx
  | .cons p m => go (p.denote ctx) m
where
  go (acc : α) : Mon → α
    | .leaf p => acc * p.denote ctx
    | .cons p m => go (acc * p.denote ctx) m

def Mon.concat (m₁ m₂ : Mon) : Mon :=
  match m₁ with
  | .leaf p => .cons p m₂
  | .cons p m₁ => .cons p (concat m₁ m₂)

def Mon.mulPow (p : Power) (m : Mon) : Mon :=
  match m with
  | .leaf p' =>
    bif p.varLt p' then
      .cons p m
    else bif p'.varLt p then
      .cons p' (.leaf p)
    else
      .leaf { x := p.x, k := p.k + p'.k }
  | .cons p' m =>
    bif p.varLt p' then
      .cons p (.cons p' m)
    else bif p'.varLt p then
      .cons p' (mulPow p m)
    else
      .cons { x := p.x, k := p.k + p'.k } m

abbrev hugeFuel := 100000
def Mon.mul (m₁ m₂ : Mon) : Mon :=
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : Mon :=
    match fuel with
    | 0 => concat m₁ m₂
    | fuel + 1 =>
      match m₁, m₂ with
      | m₁, .leaf p => m₁.mulPow p
      | .leaf p, m₂ => m₂.mulPow p
      | .cons p₁ m₁, .cons p₂ m₂ =>
        bif p₁.varLt p₂ then
          .cons p₁ (go fuel m₁ (.cons p₂ m₂))
        else bif p₂.varLt p₁ then
          .cons p₂ (go fuel (.cons p₁ m₁) m₂)
        else
          .cons { x := p₁.x, k := p₁.k + p₂.k } (go fuel m₁ m₂)

def Mon.degree : Mon → Nat
  | .leaf p => p.k
  | .cons p m => p.k + degree m

def Mon.length : Mon → Nat
  | .leaf _ => 1
  | .cons _ m => 1 + length m

def Var.revlex (x y : Var) : Ordering :=
  bif x.blt y then .gt
  else bif y.blt x then .lt
  else .eq

def powerRevlex (k₁ k₂ : Nat) : Ordering :=
  bif k₁.blt k₂ then .lt
  else bif k₂.blt k₁ then .gt
  else .eq

def Power.revLex (p₁ p₂ : Power) : Ordering :=
  p₁.x.revlex p₂.x |>.then (powerRevlex p₁.k p₂.k)

def Mon.revlex' (fuel : Nat) (m₁ m₂ : Mon) : Ordering :=
  match fuel with
  | 0 => .lt
  | fuel + 1 =>
    match m₁, m₂ with
    | .leaf p₁, .leaf p₂ => p₁.revLex p₂
    | .leaf p₁, .cons p₂ m₂ =>
      bif p₁.x.ble p₂.x  then
        .gt
      else
        revlex' fuel (.leaf p₁) m₂ |>.then .gt
    | .cons p₁ m₁, .leaf p₂ =>
      bif p₂.x.ble p₁.x then
        .lt
      else
        revlex' fuel m₁ (.leaf p₂) |>.then .lt
    | .cons p₁ m₁, .cons p₂ m₂ =>
      bif p₁.x == p₂.x then
        revlex' fuel m₁ m₂ |>.then (powerRevlex p₁.k p₂.k)
      else bif p₁.x.blt p₂.x then
        revlex' fuel m₁ (.cons p₂ m₂) |>.then .gt
      else
        revlex' fuel (.cons p₁ m₁) m₂ |>.then .lt

def Mon.revlex (m₁ m₂ : Mon) : Ordering :=
  revlex' (m₁.length + m₂.length) m₁ m₂

def Mon.grevlex (m₁ m₂ : Mon) : Ordering :=
  compare m₁.degree m₂.degree |>.then (revlex m₁ m₂)

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Mon) (p : Poly)
  deriving BEq

def Poly.denote [CommRing α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .num k => Int.cast k
  | .add k m p => Int.cast k * m.denote ctx + denote ctx p

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k' + k)
  | .add k' m p => .add k' m (addConst p k)

theorem Power.denote_eq [CommRing α] (ctx : Context α) (p : Power)
    : p.denote ctx = p.x.denote ctx ^ p.k := by
  cases p <;> simp [Power.denote] <;> split <;> simp [pow_zero, pow_succ, one_mul]

theorem Mon.denote'_go_eq_denote [CommRing α] (ctx : Context α) (a : α) (m : Mon)
    : denote'.go ctx a m = a * denote ctx m := by
  induction m generalizing a <;> simp [Mon.denote, Mon.denote'.go]
  next p' m ih =>
    simp [Mon.denote] at ih
    rw [ih, mul_assoc]

theorem Mon.denote'_eq_denote [CommRing α] (ctx : Context α) (m : Mon)
    : denote' ctx m = denote ctx m := by
  cases m <;> simp [Mon.denote, Mon.denote']
  next p m => apply denote'_go_eq_denote

theorem Mon.denote_concat [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (concat m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  induction m₁ <;> simp [concat, denote, *]
  next p₁ m₁ ih => rw [mul_assoc]

private theorem le_of_blt_false {a b : Nat} : a.blt b = false → b ≤ a := by
  intro h; apply Nat.le_of_not_gt; show ¬a < b
  rw [← Nat.blt_eq, h]; simp

private theorem eq_of_blt_false {a b : Nat} : a.blt b = false → b.blt a = false → a = b := by
  intro h₁ h₂
  replace h₁ := le_of_blt_false h₁
  replace h₂ := le_of_blt_false h₂
  exact Nat.le_antisymm h₂ h₁

theorem Mon.denote_mulPow [CommRing α] (ctx : Context α) (p : Power) (m : Mon)
    : denote ctx (mulPow p m) = p.denote ctx * m.denote ctx := by
  fun_induction mulPow <;> simp [mulPow, *]
  next => simp [denote]
  next => simp [denote]; rw [mul_comm]
  next p' h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [denote, Power.denote_eq, this, pow_add]
  next => simp [denote]
  next => simp [denote, mul_assoc, mul_comm, mul_left_comm, *]
  next h₁ h₂ =>
    have := eq_of_blt_false h₁ h₂
    simp [denote, Power.denote_eq, pow_add, this, mul_assoc]

theorem Mon.denote_mul [CommRing α] (ctx : Context α) (m₁ m₂ : Mon)
    : denote ctx (mul m₁ m₂) = m₁.denote ctx * m₂.denote ctx := by
  unfold mul
  generalize hugeFuel = fuel
  fun_induction mul.go <;> simp [mul.go, denote, denote_concat, denote_mulPow, *]
  next => rw [mul_comm]
  next => simp [mul_assoc]
  next => simp [mul_assoc, mul_left_comm, mul_comm]
  next h₁ h₂ _ =>
    have := eq_of_blt_false h₁ h₂
    simp [Power.denote_eq, pow_add, mul_assoc, mul_left_comm, mul_comm, this]

end CommRing
end Lean.Grind
