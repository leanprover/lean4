/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Linear
import Init.Data.List.BasicAux

namespace Nat.SOM

open Linear (Var hugeFuel Context Var.denote)

inductive Expr where
  | num (i : Nat)
  | var (v : Var)
  | add (a b : Expr)
  | mul (a b : Expr)
  deriving Inhabited

def Expr.denote (ctx : Context) : Expr → Nat
  | num n   => n
  | var v   => v.denote ctx
  | add a b => Nat.add (a.denote ctx) (b.denote ctx)
  | mul a b => Nat.mul (a.denote ctx) (b.denote ctx)

abbrev Mon := List Var

def Mon.denote (ctx : Context) : Mon → Nat
  | [] => 1
  | v::vs => Nat.mul (v.denote ctx) (denote ctx vs)

def Mon.mul (m₁ m₂ : Mon) : Mon :=
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : Mon :=
    match fuel with
    | 0 => m₁ ++ m₂
    | fuel + 1 =>
      match m₁, m₂ with
      | m₁, [] => m₁
      | [], m₂ => m₂
      | v₁ :: m₁, v₂ :: m₂ =>
        bif Nat.blt v₁ v₂ then
          v₁ :: go fuel m₁ (v₂ :: m₂)
        else bif Nat.blt v₂ v₁ then
          v₂ :: go fuel (v₁ :: m₁) m₂
        else
          v₁ :: v₂ :: go fuel m₁ m₂

abbrev Poly := List (Nat × Mon)

def Poly.denote (ctx : Context) : Poly → Nat
  | [] => 0
  | (k, m) :: p => Nat.add (Nat.mul k (m.denote ctx)) (denote ctx p)

def Poly.add (p₁ p₂ : Poly) : Poly :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
    match fuel with
    | 0 => p₁ ++ p₂
    | fuel + 1 =>
      match p₁, p₂ with
      | p₁, [] => p₁
      | [], p₂ => p₂
      | (k₁, m₁) :: p₁, (k₂, m₂) :: p₂ =>
        bif m₁ < m₂ then
          (k₁, m₁) :: go fuel p₁ ((k₂, m₂) :: p₂)
        else bif m₂ < m₁ then
          (k₂, m₂) :: go fuel ((k₁, m₁) :: p₁) p₂
        else bif k₁ + k₂ == 0 then
          go fuel p₁ p₂
        else
          (k₁ + k₂, m₁) :: go fuel p₁ p₂

def Poly.insertSorted (k : Nat) (m : Mon) (p : Poly) : Poly :=
  match p with
  | [] => [(k, m)]
  | (k', m') :: p => bif m < m' then (k, m) :: (k', m') :: p else (k', m') :: insertSorted k m p

def Poly.mulMon (p : Poly) (k : Nat) (m : Mon) : Poly :=
  go p []
where
  go (p : Poly) (acc : Poly) : Poly :=
    match p with
    | [] => acc
    | (k', m') :: p => go p (acc.insertSorted (k*k') (m.mul m'))

def Poly.mul (p₁ : Poly) (p₂ : Poly) : Poly :=
  go p₁ []
where
  go (p₁ : Poly) (acc : Poly) : Poly :=
    match p₁ with
    | [] => acc
    | (k, m) :: p₁ => go p₁ (acc.add (p₂.mulMon k m))

def Expr.toPoly : Expr → Poly
  | num k   => bif k == 0 then [] else [(k, [])]
  | var v   => [(1, [v])]
  | add a b => a.toPoly.add b.toPoly
  | mul a b => a.toPoly.mul b.toPoly

theorem Mon.append_denote (ctx : Context) (m₁ m₂ : Mon) : (m₁ ++ m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
  match m₁ with
  | [] => simp! [Nat.one_mul]
  | v :: m₁ => simp! [append_denote ctx m₁ m₂, Nat.mul_assoc]

theorem Mon.mul_denote (ctx : Context) (m₁ m₂ : Mon) : (m₁.mul m₂).denote ctx = m₁.denote ctx * m₂.denote ctx :=
  go hugeFuel m₁ m₂
where
  go (fuel : Nat) (m₁ m₂ : Mon) : (Mon.mul.go fuel m₁ m₂).denote ctx = m₁.denote ctx * m₂.denote ctx := by
    induction fuel generalizing m₁ m₂ with
    | zero => simp! [append_denote]
    | succ _ ih =>
      simp!
      split <;> simp!
      next v₁ m₁ v₂ m₂ =>
        by_cases hlt : Nat.blt v₁ v₂ <;> simp! [hlt, Nat.mul_assoc, ih]
        by_cases hgt : Nat.blt v₂ v₁ <;> simp! [hgt, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, ih]

theorem Poly.append_denote (ctx : Context) (p₁ p₂ : Poly) : (p₁ ++ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  match p₁ with
  | [] => simp!
  | v :: p₁ => simp! [append_denote _ p₁ p₂, Nat.add_assoc]

theorem Poly.add_denote (ctx : Context) (p₁ p₂ : Poly) : (p₁.add p₂).denote ctx = p₁.denote ctx + p₂.denote ctx :=
  go hugeFuel p₁ p₂
where
  go (fuel : Nat) (p₁ p₂ : Poly) : (Poly.add.go fuel p₁ p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
    induction fuel generalizing p₁ p₂ with
    | zero => simp! [append_denote]
    | succ _ ih =>
      simp!
      split <;> simp!
      next k₁ m₁ p₁ k₂ m₂ p₂ =>
        by_cases hlt : m₁ < m₂ <;> simp! [hlt, Nat.add_assoc, ih]
        by_cases hgt : m₂ < m₁ <;> simp! [hgt, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, ih]
        have : m₁ = m₂ := List.le_antisymm hgt hlt
        subst m₂
        by_cases heq : k₁ + k₂ == 0 <;> simp! [heq, ih]
        · simp [← Nat.add_assoc, ← Nat.right_distrib, eq_of_beq heq]
        · simp [Nat.right_distrib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Poly.denote_insertSorted (ctx : Context) (k : Nat) (m : Mon) (p : Poly) : (p.insertSorted k m).denote ctx = p.denote ctx + k * m.denote ctx := by
  match p with
  | [] => simp!
  | (k', m') :: p =>
    by_cases h : m < m' <;> simp! [h, denote_insertSorted ctx k m p, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem Poly.mulMon_denote (ctx : Context) (p : Poly) (k : Nat) (m : Mon) : (p.mulMon k m).denote ctx = p.denote ctx * k * m.denote ctx := by
  simp [mulMon, go]; simp!
where
  go (p : Poly) (acc : Poly) : (mulMon.go k m p acc).denote ctx = acc.denote ctx + p.denote ctx * k * m.denote ctx := by
   match p with
   | [] => simp!
   | (k', m') :: p =>
     simp! [go p, Nat.left_distrib, denote_insertSorted, Mon.mul_denote, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.add_assoc]

theorem Poly.mul_denote (ctx : Context) (p₁ p₂ : Poly) : (p₁.mul p₂).denote ctx = p₁.denote ctx * p₂.denote ctx := by
  simp [mul, go]; simp!
where
  go (p₁ : Poly) (acc : Poly) : (mul.go p₂ p₁ acc).denote ctx = acc.denote ctx + p₁.denote ctx * p₂.denote ctx := by
    match p₁ with
    | [] => simp!
    | (k, m) :: p₁ =>
      simp! [go p₁, Nat.left_distrib, add_denote, mulMon_denote,
             Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
             Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem Expr.toPoly_denote (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k =>
    simp!; by_cases h : k == 0 <;> simp! [*]
    simp [eq_of_beq h]
  | var v => simp!
  | add a b => simp! [Poly.add_denote, *]
  | mul a b => simp! [Poly.mul_denote, *]

theorem Expr.eq_of_toPoly_eq (ctx : Context) (a b : Expr) (h : a.toPoly == b.toPoly) : a.denote ctx = b.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [toPoly_denote] at h
  assumption

end Nat.SOM
