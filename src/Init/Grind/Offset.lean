/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Omega

namespace Lean.Grind.Offset

abbrev Var := Nat
abbrev Context := Lean.RArray Nat

def fixedVar := 100000000 -- Any big number should work here

def Var.denote (ctx : Context) (v : Var) : Nat :=
  bif v == fixedVar then 1 else ctx.get v

structure Cnstr where
  x : Var
  y : Var
  k : Nat  := 0
  l : Bool := true
  deriving Repr, DecidableEq, Inhabited

def Cnstr.denote (c : Cnstr) (ctx : Context) : Prop :=
  if c.l then
    c.x.denote ctx + c.k ≤ c.y.denote ctx
  else
    c.x.denote ctx ≤ c.y.denote ctx + c.k

def trivialCnstr : Cnstr := { x := 0, y := 0, k := 0, l := true }

@[simp] theorem denote_trivial (ctx : Context) : trivialCnstr.denote ctx := by
  simp [Cnstr.denote, trivialCnstr]

def Cnstr.trans (c₁ c₂ : Cnstr) : Cnstr :=
  if c₁.y = c₂.x then
    let { x, k := k₁, l := l₁, .. } := c₁
    let { y, k := k₂, l := l₂, .. } := c₂
    match l₁, l₂ with
    | false, false =>
      { x, y, k := k₁ + k₂, l := false }
    | false, true =>
      if k₁ < k₂ then
        { x, y, k := k₂ - k₁, l := true }
      else
        { x, y, k := k₁ - k₂, l := false }
    | true, false =>
      if k₁ < k₂ then
        { x, y, k := k₂ - k₁, l := false }
      else
        { x, y, k := k₁ - k₂, l := true }
    | true, true =>
      { x, y, k := k₁ + k₂, l := true }
  else
    trivialCnstr

@[simp] theorem Cnstr.denote_trans_easy (ctx : Context) (c₁ c₂ : Cnstr) (h : c₁.y ≠ c₂.x) : (c₁.trans c₂).denote ctx := by
  simp [*, Cnstr.trans]

@[simp] theorem Cnstr.denote_trans (ctx : Context) (c₁ c₂ : Cnstr) : c₁.denote ctx → c₂.denote ctx → (c₁.trans c₂).denote ctx := by
  by_cases c₁.y = c₂.x
  case neg => simp [*]
  simp [trans, *]
  let { x, k := k₁, l := l₁, .. } := c₁
  let { y, k := k₂, l := l₂, .. } := c₂
  simp_all; split
  · simp [denote]; omega
  · split <;> simp [denote] <;> omega
  · split <;> simp [denote] <;> omega
  · simp [denote]; omega

def Cnstr.isTrivial (c : Cnstr) : Bool := c.x == c.y && c.k == 0

theorem Cnstr.of_isTrivial (ctx : Context) (c : Cnstr) : c.isTrivial = true → c.denote ctx := by
  cases c; simp [isTrivial]; intros; simp [*, denote]

def Cnstr.isFalse (c : Cnstr) : Bool := c.x == c.y && c.k != 0 && c.l == true

theorem Cnstr.of_isFalse (ctx : Context) {c : Cnstr} : c.isFalse = true → ¬c.denote ctx := by
  cases c; simp [isFalse]; intros; simp [*, denote]; omega

def Cnstrs := List Cnstr

def Cnstrs.denoteAnd' (ctx : Context) (c₁ : Cnstr) (c₂ : Cnstrs) : Prop :=
  match c₂ with
  | [] => c₁.denote ctx
  | c::cs => c₁.denote ctx ∧ Cnstrs.denoteAnd' ctx c cs

theorem Cnstrs.denote'_trans (ctx : Context) (c₁ c : Cnstr) (cs : Cnstrs) : c₁.denote ctx → denoteAnd' ctx c cs → denoteAnd' ctx (c₁.trans c) cs := by
  induction cs
  next => simp [denoteAnd', *]; apply Cnstr.denote_trans
  next c cs ih => simp [denoteAnd']; intros; simp [*]

def Cnstrs.trans' (c₁ : Cnstr) (c₂ : Cnstrs) : Cnstr :=
  match c₂ with
  | [] => c₁
  | c::c₂ => trans' (c₁.trans c) c₂

@[simp] theorem Cnstrs.denote'_trans' (ctx : Context) (c₁ : Cnstr) (c₂ : Cnstrs) : denoteAnd' ctx c₁ c₂ → (trans' c₁ c₂).denote ctx := by
  induction c₂ generalizing c₁
  next => intros; simp_all [trans', denoteAnd']
  next c cs ih => simp [denoteAnd']; intros; simp [trans']; apply ih; apply denote'_trans <;> assumption

def Cnstrs.denoteAnd (ctx : Context) (c : Cnstrs) : Prop :=
  match c with
  | [] => True
  | c::cs => denoteAnd' ctx c cs

def Cnstrs.trans (c : Cnstrs) : Cnstr :=
  match c with
  | []    => trivialCnstr
  | c::cs => trans' c cs

theorem Cnstrs.of_denoteAnd_trans {ctx : Context} {c : Cnstrs} : c.denoteAnd ctx → c.trans.denote ctx := by
  cases c <;> simp [*, trans, denoteAnd] <;> intros <;> simp [*]

def Cnstrs.isFalse (c : Cnstrs) : Bool :=
  c.trans.isFalse

theorem Cnstrs.unsat' (ctx : Context) (c : Cnstrs) : c.isFalse = true → ¬ c.denoteAnd ctx := by
  simp [isFalse]; intro h₁ h₂
  have := of_denoteAnd_trans h₂
  have := Cnstr.of_isFalse ctx h₁
  contradiction

/-- Returns `c_1 → ... → c_n → C -/
def Cnstrs.denote (ctx : Context) (cs : Cnstrs) (C : Prop) : Prop :=
  match cs with
  | [] => C
  | c::cs => c.denote ctx → denote ctx cs C

theorem Cnstrs.not_denoteAnd'_eq (ctx : Context) (c : Cnstr) (cs : Cnstrs) (C : Prop) : (denoteAnd' ctx c cs → C) = denote ctx (c::cs) C := by
  simp [denote]
  induction cs generalizing c
  next => simp [denoteAnd', denote]
  next c' cs ih =>
    simp [denoteAnd', denote, *]

theorem Cnstrs.not_denoteAnd_eq (ctx : Context) (cs : Cnstrs) (C : Prop) : (denoteAnd ctx cs → C) = denote ctx cs C := by
  cases cs
  next => simp [denoteAnd, denote]
  next c cs => apply not_denoteAnd'_eq

def Cnstr.isImpliedBy (cs : Cnstrs) (c : Cnstr) : Bool :=
  cs.trans == c

/-! Main theorems used by `grind`. -/

/-- Auxiliary theorem used by `grind` to prove that a system of offset inequalities is unsatisfiable. -/
theorem Cnstrs.unsat (ctx : Context) (cs : Cnstrs) : cs.isFalse = true → cs.denote ctx False := by
  intro h
  rw [← not_denoteAnd_eq]
  apply unsat'
  assumption

/-- Auxiliary theorem used by `grind` to prove an implied offset inequality. -/
theorem Cnstrs.imp (ctx : Context) (cs : Cnstrs) (c : Cnstr) (h : c.isImpliedBy cs = true)  : cs.denote ctx (c.denote ctx) := by
  rw [← eq_of_beq h]
  rw [← not_denoteAnd_eq]
  apply of_denoteAnd_trans

end Lean.Grind.Offset
