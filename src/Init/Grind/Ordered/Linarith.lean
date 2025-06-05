/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind.Ordered.Module
import all Init.Data.Ord
import all Init.Data.AC
import Init.Data.RArray

/-!
Support for the linear arithmetic module for `IntModule` in `grind`
-/

namespace Lean.Grind.Linarith
abbrev Var := Nat
open IntModule

attribute [local simp] add_zero zero_add zero_hmul hmul_zero one_hmul

inductive Expr where
  | zero
  | var  (i : Var)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | neg  (a : Expr)
  | mul  (k : Int) (a : Expr)
  deriving Inhabited, BEq

abbrev Context (α : Type u) := RArray α

def Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

def Expr.denote {α} [IntModule α] (ctx : Context α) : Expr → α
  | zero      => 0
  | .var v    => v.denote ctx
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .mul k a  => k * denote ctx a
  | .neg a    => -denote ctx a

inductive Poly where
  | nil
  | add (k : Int) (v : Var) (p : Poly)
  deriving BEq

def Poly.denote {α} [IntModule α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .nil => 0
  | .add k v p => k * v.denote ctx + denote ctx p

/--
Similar to `Poly.denote`, but produces a denotation better for normalization.
-/
def Poly.denote' {α} [IntModule α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .nil => 0
  | .add 1 v p => go (v.denote ctx) p
  | .add k v p => go (k * v.denote ctx) p
where
  go (r : α)  (p : Poly) : α :=
    match p with
    | .nil => r
    | .add 1 v p => go (r + v.denote ctx) p
    | .add k v p => go (r + k * v.denote ctx) p

-- Helper instance for `ac_rfl`
local instance {α} [IntModule α] : Std.Associative (· + · : α → α → α) where
  assoc := IntModule.add_assoc
-- Helper instance for `ac_rfl`
local instance {α} [IntModule α] : Std.Commutative (· + · : α → α → α) where
  comm := IntModule.add_comm

theorem Poly.denote'_go_eq_denote {α} [IntModule α] (ctx : Context α) (p : Poly) (r : α) : denote'.go ctx r p = p.denote ctx + r := by
  induction r, p using denote'.go.induct ctx <;> simp [denote'.go, denote]
  next ih => rw [ih]; ac_rfl
  next ih => rw [ih]; ac_rfl

theorem Poly.denote'_eq_denote {α} [IntModule α] (ctx : Context α) (p : Poly) : p.denote' ctx = p.denote ctx := by
  unfold denote' <;> split <;> simp [denote, denote'_go_eq_denote] <;> ac_rfl

def Poly.insert (k : Int) (v : Var) (p : Poly) : Poly :=
  match p with
  | .nil => .add k v .nil
  | .add k' v' p =>
    bif Nat.blt v' v then
      .add k v <| .add k' v' p
    else bif Nat.beq v v' then
      if Int.add k k' == 0 then
        p
      else
        .add (Int.add k k') v' p
    else
      .add k' v' (insert k v p)

/-- Normalizes the given polynomial by fusing monomial and constants. -/
def Poly.norm (p : Poly) : Poly :=
  match p with
  | .nil => .nil
  | .add k v p => (norm p).insert k v

def Poly.append (p₁ p₂ : Poly) : Poly :=
  match p₁ with
  | .nil => p₂
  | .add k x p₁ => .add k x (append p₁ p₂)

def Poly.combine' (fuel : Nat) (p₁ p₂ : Poly) : Poly :=
  match fuel with
  | 0 => p₁.append p₂
  | fuel + 1 => match p₁, p₂ with
    | .nil, p₂ => p₂
    | p₁, .nil => p₁
    | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
      bif Nat.beq x₁ x₂ then
        let a := a₁ + a₂
        bif a == 0 then
          combine' fuel p₁ p₂
        else
          .add a x₁ (combine' fuel p₁ p₂)
      else bif Nat.blt x₂ x₁ then
        .add a₁ x₁ (combine' fuel p₁ (.add a₂ x₂ p₂))
      else
        .add a₂ x₂ (combine' fuel (.add a₁ x₁ p₁) p₂)

def Poly.combine (p₁ p₂ : Poly) : Poly :=
  combine' 100000000 p₁ p₂

/-- Converts the given expression into a polynomial. -/
def Expr.toPoly' (e : Expr) : Poly :=
  go 1 e .nil
where
  go (coeff : Int) : Expr → (Poly → Poly)
    | .zero     => id
    | .var v    => (.add coeff v ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .sub a b  => go coeff a ∘ go (-coeff) b
    | .mul k a  => bif k == 0 then id else go (Int.mul coeff k) a
    | .neg a    => go (-coeff) a

/-- Converts the given expression into a polynomial, and then normalizes it. -/
def Expr.norm (e : Expr) : Poly :=
  e.toPoly'.norm

/--
`p.mul k` multiplies all coefficients and constant of the polynomial `p` by `k`.
-/
def Poly.mul' (p : Poly) (k : Int) : Poly :=
  match p with
  | .nil => .nil
  | .add k' v p => .add (k*k') v (mul' p k)

def Poly.mul (p : Poly) (k : Int) : Poly :=
  if k == 0 then
    .nil
  else
    p.mul' k

@[simp] theorem Poly.denote_mul {α} [IntModule α] (ctx : Context α) (p : Poly) (k : Int) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp [mul]
  split
  next => simp [*, denote]
  next =>
    induction p <;> simp [mul', denote, *]
    rw [mul_hmul, hmul_add]

theorem Poly.denote_insert {α} [IntModule α] (ctx : Context α) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  fun_induction p.insert k v <;> simp [denote]
  next => ac_rfl
  next h₁ h₂ h₃ =>
    simp at h₃; simp at h₂; subst h₂
    rw [add_comm, ← add_assoc, ← add_hmul, h₃, zero_hmul, zero_add]
  next h _ => simp at h; subst h; rw [add_hmul]; ac_rfl
  next ih => rw [ih]; ac_rfl

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm {α} [IntModule α] (ctx : Context α) (p : Poly) : p.norm.denote ctx = p.denote ctx := by
  induction p <;> simp [denote, norm, add_comm, *]

attribute [local simp] Poly.denote_norm

theorem Poly.denote_append {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly) : (p₁.append p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  induction p₁ <;> simp [append, denote, *]; ac_rfl

attribute [local simp] Poly.denote_append

theorem Poly.denote_combine' {α} [IntModule α] (ctx : Context α) (fuel : Nat) (p₁ p₂ : Poly) : (p₁.combine' fuel p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction p₁.combine' fuel p₂ <;>
    simp_all +zetaDelta [denote, ← Int.add_mul]
  next h _ =>
    rw [Int.add_comm] at h
    rw [add_left_comm, add_assoc, ← add_assoc, ← add_hmul, h, zero_hmul, zero_add]
  next => rw [add_hmul]; ac_rfl
  all_goals ac_rfl

theorem Poly.denote_combine {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly) : (p₁.combine p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  simp [combine, denote_combine']

attribute [local simp] Poly.denote_combine

theorem Expr.denote_toPoly'_go {α} [IntModule α] {k p} (ctx : Context α) (e : Expr)
    : (toPoly'.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
  induction k, e using Expr.toPoly'.go.induct generalizing p <;> simp [toPoly'.go, denote, Poly.denote, *, hmul_add]
  next => ac_rfl
  next => rw [sub_eq_add_neg, neg_hmul, hmul_add, hmul_neg]; ac_rfl
  next h => simp at h; subst h; simp
  next ih => simp at ih; rw [ih, mul_hmul]
  next => rw [hmul_neg, neg_hmul]

theorem Expr.denote_norm {α} [IntModule α] (ctx : Context α) (e : Expr) : e.norm.denote ctx = e.denote ctx := by
  simp [norm, toPoly', Expr.denote_toPoly'_go, Poly.denote]

attribute [local simp] Expr.denote_norm

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    next ih =>
      intro _ _ h
      exact ih h
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    assumption

attribute [local simp] Poly.denote'_eq_denote

end Lean.Grind.Linarith
