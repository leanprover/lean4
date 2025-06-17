/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
import Init.Grind.Ordered.Module
import Init.Grind.Ordered.Ring
import Init.Grind.Ring.Field
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

def Poly.coeff (p : Poly) (x : Var) : Int :=
  match p with
  | .add a y p => bif x == y then a else coeff p x
  | .nil => 0

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

def Poly.leadCoeff (p : Poly) : Int :=
  match p with
  | .add a _ _ => a
  | _ => 1

open IntModule.IsOrdered

/-!
Helper theorems for conflict resolution during model construction.
-/

private theorem le_add_le {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] {a b : α}
    (h₁ : a ≤ 0) (h₂ : b ≤ 0) : a + b ≤ 0 := by
  replace h₁ := add_le_left h₁ b; simp at h₁
  exact Preorder.le_trans h₁ h₂

private theorem le_add_lt {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] {a b : α}
    (h₁ : a ≤ 0) (h₂ : b < 0) : a + b < 0 := by
  replace h₁ := add_le_left h₁ b; simp at h₁
  exact Preorder.lt_of_le_of_lt h₁ h₂

private theorem lt_add_lt {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] {a b : α}
    (h₁ : a < 0) (h₂ : b < 0) : a + b < 0 := by
  replace h₁ := add_lt_left h₁ b; simp at h₁
  exact Preorder.lt_trans h₁ h₂

private theorem coe_natAbs_nonneg (a : Int) : (a.natAbs : Int) ≥ 0 := by
  exact Int.natCast_nonneg a.natAbs

def le_le_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  p₃ == (p₁.mul a₂ |>.combine (p₂.mul a₁))

theorem le_le_combine {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : le_le_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_le_combine_cert]; intro _ h₁ h₂; subst p₃; simp
  replace h₁ := hmul_nonpos (coe_natAbs_nonneg p₂.leadCoeff) h₁
  replace h₂ := hmul_nonpos (coe_natAbs_nonneg p₁.leadCoeff) h₂
  exact le_add_le h₁ h₂

def le_lt_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  a₁ > (0 : Int) && p₃ == (p₁.mul a₂ |>.combine (p₂.mul a₁))

theorem le_lt_combine {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : le_lt_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx < 0 → p₃.denote' ctx < 0 := by
  simp [-Int.natAbs_pos, -Int.ofNat_pos, le_lt_combine_cert]; intro hp _ h₁ h₂; subst p₃; simp
  replace h₁ := hmul_nonpos (coe_natAbs_nonneg p₂.leadCoeff) h₁
  replace h₂ := hmul_neg_iff (↑p₁.leadCoeff.natAbs) h₂ |>.mpr hp
  exact le_add_lt h₁ h₂

def lt_lt_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  a₂ > (0 : Int) && a₁ > (0 : Int) && p₃ == (p₁.mul a₂ |>.combine (p₂.mul a₁))

theorem lt_lt_combine {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : lt_lt_combine_cert p₁ p₂ p₃ → p₁.denote' ctx < 0 → p₂.denote' ctx < 0 → p₃.denote' ctx < 0 := by
  simp [-Int.natAbs_pos, -Int.ofNat_pos, lt_lt_combine_cert]; intro hp₁ hp₂ _ h₁ h₂; subst p₃; simp
  replace h₁ := hmul_neg_iff (↑p₂.leadCoeff.natAbs) h₁ |>.mpr hp₁
  replace h₂ := hmul_neg_iff (↑p₁.leadCoeff.natAbs) h₂ |>.mpr hp₂
  exact lt_add_lt h₁ h₂

def diseq_split_cert (p₁ p₂ : Poly) : Bool :=
  p₂ == p₁.mul (-1)

-- We need `LinearOrder` to use `trichotomy`
theorem diseq_split {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ : Poly)
    : diseq_split_cert p₁ p₂ → p₁.denote' ctx ≠ 0 → p₁.denote' ctx < 0 ∨ p₂.denote' ctx < 0 := by
  simp [diseq_split_cert]; intro _ h₁; subst p₂; simp
  cases LinearOrder.trichotomy (p₁.denote ctx) 0
  next h => exact Or.inl h
  next h =>
    apply Or.inr
    simp [h₁] at h
    rw [← neg_pos_iff, neg_hmul, neg_neg, one_hmul]; assumption

theorem diseq_split_resolve {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ : Poly)
    : diseq_split_cert p₁ p₂ → p₁.denote' ctx ≠ 0 → ¬p₁.denote' ctx < 0 → p₂.denote' ctx < 0 := by
  intro h₁ h₂ h₃
  exact (diseq_split ctx p₁ p₂ h₁ h₂).resolve_left h₃

/-!
Helper theorems for internalizing facts into the linear arithmetic procedure
-/

def norm_cert (lhs rhs : Expr) (p : Poly) :=
  p == (lhs.sub rhs).norm

theorem eq_norm {α} [IntModule α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote' ctx = 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]

theorem le_of_eq {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote ctx = rhs.denote ctx → p.denote' ctx ≤ 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  apply Preorder.le_refl

theorem diseq_norm {α} [IntModule α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote ctx ≠ rhs.denote ctx → p.denote' ctx ≠ 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  intro h
  replace h := congrArg (rhs.denote ctx + ·) h; simp [sub_eq_add_neg] at h
  rw [add_left_comm, ← sub_eq_add_neg, sub_self, add_zero] at h
  contradiction

theorem le_norm {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote ctx ≤ rhs.denote ctx → p.denote' ctx ≤ 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  replace h₁ := add_le_left h₁ (-rhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem lt_norm {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote ctx < rhs.denote ctx → p.denote' ctx < 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  replace h₁ := add_lt_left h₁ (-rhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_le_norm {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert rhs lhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → p.denote' ctx < 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  replace h₁ := LinearOrder.lt_of_not_le h₁
  replace h₁ := add_lt_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_lt_norm {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert rhs lhs p → ¬ lhs.denote ctx < rhs.denote ctx → p.denote' ctx ≤ 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]
  replace h₁ := LinearOrder.le_of_not_lt h₁
  replace h₁ := add_le_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

-- If the module does not have a linear order, we can still put the expressions in polynomial forms

theorem not_le_norm' {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → ¬ lhs.denote ctx ≤ rhs.denote ctx → ¬ p.denote' ctx ≤ 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]; intro h
  replace h := add_le_right (rhs.denote ctx) h
  rw [sub_eq_add_neg, add_left_comm, ← sub_eq_add_neg, sub_self] at h; simp at h
  contradiction

theorem not_lt_norm' {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → ¬ lhs.denote ctx < rhs.denote ctx → ¬ p.denote' ctx < 0 := by
  simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]; intro h
  replace h := add_lt_right (rhs.denote ctx) h
  rw [sub_eq_add_neg, add_left_comm, ← sub_eq_add_neg, sub_self] at h; simp at h
  contradiction

/-!
Equality detection
-/
def eq_of_le_ge_cert (p₁ p₂ : Poly) : Bool :=
  p₂ == p₁.mul (-1)

theorem eq_of_le_ge {α} [IntModule α] [PartialOrder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ : Poly) (p₂ : Poly)
    : eq_of_le_ge_cert p₁ p₂ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₁.denote' ctx = 0 := by
  simp [eq_of_le_ge_cert]
  intro; subst p₂; simp
  intro h₁ h₂
  replace h₂ := add_le_left h₂ (p₁.denote ctx)
  rw [add_comm, neg_hmul, one_hmul, ← sub_eq_add_neg, sub_self, zero_add] at h₂
  exact PartialOrder.le_antisymm h₁ h₂

/-!
Helper theorems for closing the goal
-/

theorem diseq_unsat {α} [IntModule α] (ctx : Context α) : (Poly.nil).denote ctx ≠ 0 → False := by
  simp [Poly.denote]

theorem lt_unsat {α} [IntModule α] [Preorder α] (ctx : Context α) : (Poly.nil).denote ctx < 0 → False := by
  simp [Poly.denote]; intro h
  have := Preorder.lt_iff_le_not_le.mp h
  simp at this

def zero_lt_one_cert (p : Poly) : Bool :=
  p == .add (-1) 0 .nil

theorem zero_lt_one {α} [Ring α] [Preorder α] [Ring.IsOrdered α] (ctx : Context α) (p : Poly)
    : zero_lt_one_cert p → (0 : Var).denote ctx = One.one → p.denote' ctx < 0 := by
  simp [zero_lt_one_cert]; intro _ h; subst p; simp [Poly.denote, h, One.one, neg_hmul]
  rw [neg_lt_iff, neg_zero]; apply Ring.IsOrdered.zero_lt_one

def zero_ne_one_cert (p : Poly) : Bool :=
  p == .add 1 0 .nil

theorem zero_ne_one_of_ord_ring {α} [Ring α] [Preorder α] [Ring.IsOrdered α] (ctx : Context α) (p : Poly)
    : zero_ne_one_cert p → (0 : Var).denote ctx = One.one → p.denote' ctx ≠ 0 := by
  simp [zero_ne_one_cert]; intro _ h; subst p; simp [Poly.denote, h, One.one]
  intro h; have := Ring.IsOrdered.zero_lt_one (R := α); simp [h, Preorder.lt_irrefl] at this

theorem zero_ne_one_of_field {α} [Field α] (ctx : Context α) (p : Poly)
    : zero_ne_one_cert p → (0 : Var).denote ctx = One.one → p.denote' ctx ≠ 0 := by
  simp [zero_ne_one_cert]; intro _ h; subst p; simp [Poly.denote, h, One.one]
  intro h; have := Field.zero_ne_one (α := α); simp [h] at this

theorem zero_ne_one_of_char0 {α} [Ring α] [IsCharP α 0] (ctx : Context α) (p : Poly)
    : zero_ne_one_cert p → (0 : Var).denote ctx = One.one → p.denote' ctx ≠ 0 := by
  simp [zero_ne_one_cert]; intro _ h; subst p; simp [Poly.denote, h, One.one]
  intro h; have := IsCharP.intCast_eq_zero_iff (α := α) 0 1; simp [Ring.intCast_one] at this
  contradiction

def zero_ne_one_of_charC_cert (c : Nat) (p : Poly) : Bool :=
  (c:Int) > 1 && p == .add 1 0 .nil

theorem zero_ne_one_of_charC {α c} [Ring α] [IsCharP α c] (ctx : Context α) (p : Poly)
    : zero_ne_one_of_charC_cert c p → (0 : Var).denote ctx = One.one → p.denote' ctx ≠ 0 := by
  simp [zero_ne_one_of_charC_cert]; intro hc _ h; subst p; simp [Poly.denote, h, One.one]
  intro h; have h' := IsCharP.intCast_eq_zero_iff (α := α) c 1; simp [Ring.intCast_one] at h'
  replace h' := h'.mp h
  have := Int.emod_eq_of_lt (by decide) hc
  simp [this] at h'

/-!
Coefficient normalization
-/

def eq_neg_cert (p₁ p₂ : Poly) :=
  p₂ == p₁.mul (-1)

theorem eq_neg {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly)
    : eq_neg_cert p₁ p₂ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp [eq_neg_cert]; intros; simp [*]

def eq_coeff_cert (p₁ p₂ : Poly) (k : Nat) :=
  k != 0 && p₁ == p₂.mul k

theorem eq_coeff {α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α) (p₁ p₂ : Poly) (k : Nat)
    : eq_coeff_cert p₁ p₂ k → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp [eq_coeff_cert]; intro h _; subst p₁; simp [*]
  exact no_nat_zero_divisors k (p₂.denote ctx) h

def coeff_cert (p₁ p₂ : Poly) (k : Nat) :=
  k > 0 && p₁ == p₂.mul k

theorem le_coeff {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ : Poly) (k : Nat)
    : coeff_cert p₁ p₂ k → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 := by
  simp [coeff_cert]; intro h _; subst p₁; simp
  have : ↑k > (0 : Int) := Int.natCast_pos.mpr h
  intro h₁; apply Classical.byContradiction
  intro h₂; replace h₂ := LinearOrder.lt_of_not_le h₂
  replace h₂ := IsOrdered.hmul_pos_iff (↑k) h₂ |>.mpr this
  exact Preorder.lt_irrefl 0 (Preorder.lt_of_lt_of_le h₂ h₁)

theorem lt_coeff {α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α) (p₁ p₂ : Poly) (k : Nat)
    : coeff_cert p₁ p₂ k → p₁.denote' ctx < 0 → p₂.denote' ctx < 0 := by
  simp [coeff_cert]; intro h _; subst p₁; simp
  have : ↑k > (0 : Int) := Int.natCast_pos.mpr h
  intro h₁; apply Classical.byContradiction
  intro h₂; replace h₂ := LinearOrder.le_of_not_lt h₂
  replace h₂ := IsOrdered.hmul_nonneg (Int.le_of_lt this) h₂
  exact Preorder.lt_irrefl 0 (Preorder.lt_of_le_of_lt h₂ h₁)

theorem diseq_neg {α} [IntModule α] (ctx : Context α) (p p' : Poly) : p' == p.mul (-1) → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp; intro _ _; subst p'; simp [neg_hmul]
  intro h; replace h := congrArg (- ·) h; simp [neg_neg, neg_zero] at h
  contradiction

/-!
Substitution
-/

def eq_diseq_subst_cert (k₁ k₂ : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  k₁.natAbs ≠ 0 && p₃ == (p₁.mul k₂ |>.combine (p₂.mul k₁))

theorem eq_diseq_subst {α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α) (k₁ k₂ : Int) (p₁ p₂ p₃ : Poly)
    : eq_diseq_subst_cert k₁ k₂ p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [eq_diseq_subst_cert, - Int.natAbs_eq_zero, -Int.natCast_eq_zero]; intro hne _ h₁ h₂; subst p₃
  simp [h₁, h₂]; intro h₃
  have :  k₁.natAbs * Poly.denote ctx p₂ = 0 := by
    have : (k₁.natAbs : Int) * Poly.denote ctx p₂ = 0 := by
      cases Int.natAbs_eq_iff.mp (Eq.refl k₁.natAbs)
      next h => rw [← h]; assumption
      next h => replace h := congrArg (- ·) h; simp at h; rw [← h, IntModule.neg_hmul, h₃, IntModule.neg_zero]
    exact this
  have := no_nat_zero_divisors (k₁.natAbs) (p₂.denote ctx) hne this
  contradiction

def eq_diseq_subst1_cert (k : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  p₃ == (p₁.mul k |>.combine p₂)

/-
Special case of `diseq_eq_subst` where leading coefficient `c₁` of `p₁` is `-k*c₂`, where
`c₂` is the leading coefficient of `p₂`.
-/
theorem eq_diseq_subst1 {α} [IntModule α] (ctx : Context α) (k : Int) (p₁ p₂ p₃ : Poly)
    : eq_diseq_subst1_cert k p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [eq_diseq_subst1_cert]; intro _ h₁ h₂; subst p₃
  simp [h₁, h₂]

def eq_le_subst_cert (x : Var) (p₁ p₂ p₃ : Poly) :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  a ≥ 0 && p₃ == (p₂.mul a |>.combine (p₁.mul (-b)))

theorem eq_le_subst {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (x : Var) (p₁ p₂ p₃ : Poly)
    : eq_le_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [eq_le_subst_cert]; intro h _ h₁ h₂; subst p₃; simp [h₁]
  exact hmul_nonpos h h₂

def eq_lt_subst_cert (x : Var) (p₁ p₂ p₃ : Poly) :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  a > 0 && p₃ == (p₂.mul a |>.combine (p₁.mul (-b)))

theorem eq_lt_subst {α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α) (x : Var) (p₁ p₂ p₃ : Poly)
    : eq_lt_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx < 0 → p₃.denote' ctx < 0 := by
  simp [eq_lt_subst_cert]; intro h _ h₁ h₂; subst p₃; simp [h₁]
  exact IsOrdered.hmul_neg_iff (p₁.coeff x) h₂ |>.mpr h

def eq_eq_subst_cert (x : Var) (p₁ p₂ p₃ : Poly) :=
  let a := p₁.coeff x
  let b := p₂.coeff x
  p₃ == (p₂.mul a |>.combine (p₁.mul (-b)))

theorem eq_eq_subst {α} [IntModule α] (ctx : Context α) (x : Var) (p₁ p₂ p₃ : Poly)
    : eq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst_cert]; intro _ h₁ h₂; subst p₃; simp [h₁, h₂]

end Lean.Grind.Linarith
