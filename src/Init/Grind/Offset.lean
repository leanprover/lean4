/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Omega

namespace Lean.Grind

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
  deriving Repr, BEq, Inhabited

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

def Certificate := List Cnstr

def Certificate.denote' (ctx : Context) (c₁ : Cnstr) (c₂ : Certificate) : Prop :=
  match c₂ with
  | [] => c₁.denote ctx
  | c::cs => c₁.denote ctx ∧ Certificate.denote' ctx c cs

theorem Certificate.denote'_trans (ctx : Context) (c₁ c : Cnstr) (cs : Certificate) : c₁.denote ctx → denote' ctx c cs → denote' ctx (c₁.trans c) cs := by
  induction cs
  next => simp [denote', *]; apply Cnstr.denote_trans
  next c cs ih => simp [denote']; intros; simp [*]

def Certificate.trans' (c₁ : Cnstr) (c₂ : Certificate) : Cnstr :=
  match c₂ with
  | [] => c₁
  | c::c₂ => trans' (c₁.trans c) c₂

@[simp] theorem Certificate.denote'_trans' (ctx : Context) (c₁ : Cnstr) (c₂ : Certificate) : denote' ctx c₁ c₂ → (trans' c₁ c₂).denote ctx := by
  induction c₂ generalizing c₁
  next => intros; simp_all [trans', denote']
  next c cs ih => simp [denote']; intros; simp [trans']; apply ih; apply denote'_trans <;> assumption

def Certificate.denote (ctx : Context) (c : Certificate) : Prop :=
  match c with
  | [] => True
  | c::cs => denote' ctx c cs

def Certificate.trans (c : Certificate) : Cnstr :=
  match c with
  | []    => trivialCnstr
  | c::cs => trans' c cs

theorem Certificate.denote_trans {ctx : Context} {c : Certificate} : c.denote ctx → c.trans.denote ctx := by
  cases c <;> simp [*, trans, Certificate.denote] <;> intros <;> simp [*]

def Certificate.isFalse (c : Certificate) : Bool :=
  c.trans.isFalse

theorem Certificate.unsat (ctx : Context) (c : Certificate) : c.isFalse = true → ¬ c.denote ctx := by
  simp [isFalse]; intro h₁ h₂
  have := Certificate.denote_trans h₂
  have := Cnstr.of_isFalse ctx h₁
  contradiction

theorem Certificate.imp (ctx : Context) (c : Certificate) : c.denote ctx → c.trans.denote ctx := by
  apply denote_trans

end Lean.Grind
