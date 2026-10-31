/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Ring
public import Init.Grind.Ring.Field
public import Init.Data.Int.Kernel
import all Init.Data.Ord.Basic
import all Init.Data.AC
import Init.LawfulBEqTactics
public import Init.Data.Bool
public import Init.Data.RArray
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Nat.Lemmas
import Init.Grind.Ordered.Order
import Init.Omega
import Init.WFTactics
import Init.Data.Int.Repr

@[expose] public section

open Std

/-!
Support for the linear arithmetic module for `IntModule` in `grind`
-/

namespace Lean.Grind.Linarith
abbrev Var := Nat
open AddCommMonoid AddCommGroup NatModule IntModule

attribute [local simp] add_zero zero_add zero_zsmul zero_nsmul zsmul_zero one_zsmul

inductive Expr where
  | zero
  | var  (i : Var)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | neg  (a : Expr)
  | natMul  (k : Nat) (a : Expr)
  | intMul  (k : Int) (a : Expr)
  deriving Inhabited, BEq, Repr

abbrev Context (α : Type u) := RArray α

abbrev Var.denote {α} (ctx : Context α) (v : Var) : α :=
  ctx.get v

abbrev Expr.denote {α} [IntModule α] (ctx : Context α) : Expr → α
  | zero      => 0
  | .var v    => v.denote ctx
  | .add a b  => denote ctx a + denote ctx b
  | .sub a b  => denote ctx a - denote ctx b
  | .natMul k a  => k • denote ctx a
  | .intMul k a  => k • denote ctx a
  | .neg a    => -denote ctx a

/--
`Expr.denote` for kernel reduction. The theorems that take hypotheses about user terms state them
with `Expr.denote_k`, so that the kernel unfolds `Expr.rec` instead of `Expr.denote`'s `brecOn`.
-/
noncomputable def Expr.denote_k {α} [IntModule α] (ctx : Context α) (e : Expr) : α :=
  Expr.rec 0 (fun v => v.denote ctx) (fun _ _ a b => a + b) (fun _ _ a b => a - b)
    (fun _ a => -a) (fun k _ a => k • a) (fun k _ a => k • a) e

@[simp] theorem Expr.denote_k_eq_denote {α} [IntModule α] (ctx : Context α) (e : Expr) :
    e.denote_k ctx = e.denote ctx := by
  induction e with
  | zero => rfl
  | var => rfl
  | add a b iha ihb => show a.denote_k ctx + b.denote_k ctx = _; rw [iha, ihb]
  | sub a b iha ihb => show a.denote_k ctx - b.denote_k ctx = _; rw [iha, ihb]
  | neg a ih => show -a.denote_k ctx = _; rw [ih]
  | natMul k a ih => show k • a.denote_k ctx = _; rw [ih]
  | intMul k a ih => show k • a.denote_k ctx = _; rw [ih]

inductive Poly where
  | nil
  | add (k : Int) (v : Var) (p : Poly)
  deriving BEq, ReflBEq, LawfulBEq, Repr

abbrev Poly.denote {α} [IntModule α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .nil => 0
  | .add k v p => k • v.denote ctx + denote ctx p

abbrev Poly.denote'.go {α} [IntModule α] (ctx : Context α) (r : α) (p : Poly) : α :=
    match p with
    | .nil => r
    | .add 1 v p => go ctx (r + v.denote ctx) p
    | .add k v p => go ctx (r + k • v.denote ctx) p

/--
Similar to `Poly.denote`, but produces a denotation better for normalization.
-/
abbrev Poly.denote' {α} [IntModule α] (ctx : Context α) (p : Poly) : α :=
  match p with
  | .nil => 0
  | .add 1 v p => denote'.go ctx (v.denote ctx) p
  | .add k v p => denote'.go ctx (k • v.denote ctx) p

-- Helper instance for `ac_rfl`
local instance {α} [IntModule α] : Std.Associative (· + · : α → α → α) where
  assoc := AddCommMonoid.add_assoc
-- Helper instance for `ac_rfl`
local instance {α} [IntModule α] : Std.Commutative (· + · : α → α → α) where
  comm := AddCommMonoid.add_comm

set_option allowUnsafeReducibility true in
attribute [semireducible] Poly.denote' Poly.denote'.go in
private theorem Poly.denote'_go_eq_denote {α} [IntModule α] (ctx : Context α) (p : Poly) (r : α) : denote'.go ctx r p = p.denote ctx + r := by
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

def Poly.combine (p₁ p₂ : Poly) : Poly :=
  match p₁, p₂ with
    | .nil, p₂ => p₂
    | p₁, .nil => p₁
    | .add a₁ x₁ p₁, .add a₂ x₂ p₂ =>
      bif Nat.beq x₁ x₂ then
        let a := a₁ + a₂
        bif a == 0 then
          combine p₁ p₂
        else
          .add a x₁ (combine p₁ p₂)
      else bif Nat.blt x₂ x₁ then
        .add a₁ x₁ (combine p₁ (.add a₂ x₂ p₂))
      else
        .add a₂ x₂ (combine (.add a₁ x₁ p₁) p₂)
  termination_by sizeOf p₁ + sizeOf p₂

/-- Converts the given expression into a polynomial. -/
def Expr.toPoly' (e : Expr) : Poly :=
  go 1 e .nil
where
  go (coeff : Int) : Expr → (Poly → Poly)
    | .zero     => id
    | .var v    => (.add coeff v ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .sub a b  => go coeff a ∘ go (-coeff) b
    | .natMul k a  => bif k == 0 then id else go (Int.mul coeff k) a
    | .intMul k a  => bif k == 0 then id else go (Int.mul coeff k) a
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

@[simp] theorem Poly.denote_mul {α} [IntModule α] (ctx : Context α) (p : Poly) (k : Int) : (p.mul k).denote ctx = k • p.denote ctx := by
  simp [mul]
  split
  next => simp [*, denote]
  next =>
    induction p <;> simp [mul', denote, *]
    rw [mul_zsmul, zsmul_add]

theorem Poly.denote_insert {α} [IntModule α] (ctx : Context α) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k • v.denote ctx := by
  fun_induction p.insert k v <;> simp [denote]
  next => ac_rfl
  next h₁ h₂ h₃ =>
    simp at h₃; simp at h₂; subst h₂
    rw [add_comm, ← add_assoc, ← add_zsmul, h₃, zero_zsmul, zero_add]
  next h _ => simp at h; subst h; rw [add_zsmul]; ac_rfl
  next ih => rw [ih]; ac_rfl

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm {α} [IntModule α] (ctx : Context α) (p : Poly) : p.norm.denote ctx = p.denote ctx := by
  induction p <;> simp [denote, norm, add_comm, *]

attribute [local simp] Poly.denote_norm

theorem Poly.denote_append {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly) : (p₁.append p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  induction p₁ <;> simp [append, denote, *]; ac_rfl

attribute [local simp] Poly.denote_append

theorem Poly.denote_combine {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly) : (p₁.combine p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  fun_induction p₁.combine p₂ <;>
    simp_all +zetaDelta [denote]
  next h _ =>
    rw [Int.add_comm] at h
    rw [add_left_comm, add_assoc, ← add_assoc, ← add_zsmul, h, zero_zsmul, zero_add]
  next => rw [add_zsmul]; ac_rfl
  all_goals ac_rfl

attribute [local simp] Poly.denote_combine

private theorem Expr.denote_toPoly'_go {α} [IntModule α] {k p} (ctx : Context α) (e : Expr)
    : (toPoly'.go k e p).denote ctx = k • e.denote ctx + p.denote ctx := by
  induction k, e using Expr.toPoly'.go.induct generalizing p <;> simp [toPoly'.go, denote, Poly.denote, *, zsmul_add]
  next => ac_rfl
  next => rw [sub_eq_add_neg, neg_zsmul, zsmul_add, zsmul_neg]; ac_rfl
  next h => simp at h; subst h; simp
  next ih => simp at ih; rw [ih, mul_zsmul, zsmul_natCast_eq_nsmul]
  next ih => simp at ih; simp [ih]
  next ih => simp at ih; rw [ih, mul_zsmul]
  next => rw [zsmul_neg, neg_zsmul]

theorem Expr.denote_norm {α} [IntModule α] (ctx : Context α) (e : Expr) : e.norm.denote ctx = e.denote ctx := by
  simp [norm, toPoly', Expr.denote_toPoly'_go, Poly.denote]

attribute [local simp] Expr.denote_norm
attribute [local simp] Poly.denote'_eq_denote

/-!
Kernel-reduction variants of the polynomial functions used by the certificates, written with
recursors, `Bool.rec`, and the operations of `Init.Data.Int.Kernel`.
-/

protected noncomputable def Poly.beq' (p₁ : Poly) : Poly → Bool :=
  Poly.rec
    (fun p₂ => Poly.rec true (fun _ _ _ _ => false) p₂)
    (fun k₁ v₁ _ ih p₂ => Poly.rec false
      (fun k₂ v₂ p₂ _ => Bool.rec false (Bool.rec false (ih p₂) (Nat.beq v₁ v₂)) (Int.beq' k₁ k₂)) p₂)
    p₁

@[simp] theorem Poly.beq'_eq (p₁ p₂ : Poly) : p₁.beq' p₂ = (p₁ = p₂) := by
  induction p₁ generalizing p₂ with
  | nil => cases p₂ <;> simp [Poly.beq']
  | add k₁ v₁ p₁ ih =>
    cases p₂ with
    | nil => simp [Poly.beq']
    | add k₂ v₂ p₂ =>
      change (Int.beq' k₁ k₂ && (Nat.beq v₁ v₂ && p₁.beq' p₂)) = (_ = _)
      simp [ih, Nat.beq_eq]

noncomputable def Poly.mul_k (p : Poly) (k : Int) : Poly :=
  Bool.rec (Poly.rec .nil (fun k' v _ ih => .add (Int.mul_k k k') v ih) p) .nil (Int.beqZero_k k)

@[simp] theorem Poly.mul_k_eq (p : Poly) (k : Int) : p.mul_k k = p.mul k := by
  unfold mul_k mul; rw [Int.beqZero_k_eq]
  by_cases h : k = 0
  · subst h; rfl
  · have : (k == 0) = false := by simpa using h
    rw [this]; simp only [Bool.false_eq_true, ite_false]
    induction p with
    | nil => rfl
    | add k' v p ih => show Poly.add (Int.mul_k k k') v _ = _; rw [ih, Int.mul_k_eq]; rfl

noncomputable def Poly.combine_k (p₁ : Poly) : Poly → Poly :=
  Poly.rec (motive := fun _ => Poly → Poly)
    (fun p₂ => p₂)
    (fun a₁ x₁ p₁ ih₁ p₂ =>
      Poly.rec (motive := fun _ => Poly)
        (.add a₁ x₁ p₁)
        (fun a₂ x₂ p₂ ih₂ =>
          Bool.rec
            (Bool.rec (.add a₂ x₂ ih₂) (.add a₁ x₁ (ih₁ (.add a₂ x₂ p₂))) (Nat.blt x₂ x₁))
            (Bool.rec (.add (Int.add_k a₁ a₂) x₁ (ih₁ p₂)) (ih₁ p₂) (Int.beqZero_k (Int.add_k a₁ a₂)))
            (Nat.beq x₁ x₂))
        p₂)
    p₁

theorem Poly.combine_k_add_add (a₁ : Int) (x₁ : Var) (p₁ : Poly) (a₂ : Int) (x₂ : Var) (p₂ : Poly) :
    (Poly.add a₁ x₁ p₁).combine_k (.add a₂ x₂ p₂) =
      Bool.rec
        (Bool.rec (.add a₂ x₂ ((Poly.add a₁ x₁ p₁).combine_k p₂)) (.add a₁ x₁ (p₁.combine_k (.add a₂ x₂ p₂))) (Nat.blt x₂ x₁))
        (Bool.rec (.add (Int.add_k a₁ a₂) x₁ (p₁.combine_k p₂)) (p₁.combine_k p₂) (Int.beqZero_k (Int.add_k a₁ a₂)))
        (Nat.beq x₁ x₂) := rfl

@[simp] theorem Poly.combine_k_eq (p₁ p₂ : Poly) : p₁.combine_k p₂ = p₁.combine p₂ := by
  induction p₁ generalizing p₂ with
  | nil => simp [combine_k, combine]
  | add a₁ x₁ p₁ ih₁ =>
    induction p₂ with
    | nil => simp [combine_k, combine]
    | add a₂ x₂ p₂ ih₂ =>
      rw [combine_k_add_add, combine]
      change _ = (bif Nat.beq x₁ x₂ then
        bif (a₁ + a₂ == 0) then p₁.combine p₂ else .add (a₁ + a₂) x₁ (p₁.combine p₂)
        else bif Nat.blt x₂ x₁ then .add a₁ x₁ (p₁.combine (.add a₂ x₂ p₂))
        else .add a₂ x₂ ((Poly.add a₁ x₁ p₁).combine p₂))
      rw [Int.beqZero_k_eq, Int.add_k_eq, Int.add_def]
      cases Nat.beq x₁ x₂ <;> cases Nat.blt x₂ x₁ <;> cases (a₁ + a₂ == 0) <;>
        simp_all

@[simp] theorem Poly.denote_combine_k {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly) :
    (p₁.combine_k p₂).denote ctx = p₁.denote ctx + p₂.denote ctx := by
  induction p₁ generalizing p₂ with
  | nil => show p₂.denote ctx = _; simp [denote, zero_add]
  | add a₁ x₁ p₁ ih₁ =>
    induction p₂ with
    | nil => show (Poly.add a₁ x₁ p₁).denote ctx = _; simp [denote, add_zero]
    | add a₂ x₂ p₂ ih₂ =>
      rw [combine_k_add_add]
      cases h₁ : Nat.beq x₁ x₂
      · cases h₂ : Nat.blt x₂ x₁
        · show (Poly.add a₂ x₂ _).denote ctx = _
          simp only [denote] at ih₂ ⊢; rw [ih₂]; ac_rfl
        · show (Poly.add a₁ x₁ _).denote ctx = _
          simp only [denote, ih₁]; ac_rfl
      · rw [Nat.beq_eq] at h₁; subst h₁
        cases h₃ : Int.beqZero_k (Int.add_k a₁ a₂)
        · show (Poly.add _ x₁ _).denote ctx = _
          simp only [denote, ih₁, Int.add_k_eq, Int.add_def, add_zsmul]; ac_rfl
        · rw [Int.beqZero_k_eq, Int.add_k_eq, Int.add_def, beq_iff_eq] at h₃
          show (p₁.combine_k p₂).denote ctx = _
          simp only [denote, ih₁]
          have : a₁ • x₁.denote ctx + a₂ • x₁.denote ctx = 0 := by rw [← add_zsmul, h₃, zero_zsmul]
          rw [show a₁ • Var.denote ctx x₁ + Poly.denote ctx p₁ + (a₂ • Var.denote ctx x₁ + Poly.denote ctx p₂)
            = (a₁ • x₁.denote ctx + a₂ • x₁.denote ctx) + (p₁.denote ctx + p₂.denote ctx) by ac_rfl, this, zero_add]

noncomputable def Poly.coeff_k (p : Poly) (x : Var) : Int :=
  Poly.rec 0 (fun a y _ ih => Bool.rec ih a (Nat.beq x y)) p

@[simp] theorem Poly.coeff_k_eq (p : Poly) (x : Var) : p.coeff_k x = p.coeff x := by
  induction p with
  | nil => rfl
  | add a y p ih =>
    show Bool.rec (motive := fun _ => Int) (p.coeff_k x) a (Nat.beq x y) = (bif Nat.beq x y then a else p.coeff x)
    rw [ih]; cases Nat.beq x y <;> rfl

noncomputable def Poly.insert_k (k : Int) (v : Var) (p : Poly) : Poly :=
  Poly.rec (.add k v .nil)
    (fun k' v' p ih => Bool.rec
      (Bool.rec (.add k' v' ih)
        (Bool.rec (.add (Int.add_k k k') v' p) p (Int.beqZero_k (Int.add_k k k')))
        (Nat.beq v v'))
      (.add k v (.add k' v' p))
      (Nat.blt v' v))
    p

@[simp] theorem Poly.insert_k_eq (k : Int) (v : Var) (p : Poly) : p.insert_k k v = p.insert k v := by
  induction p with
  | nil => rfl
  | add k' v' p ih =>
    show Bool.rec (motive := fun _ => Poly)
      (Bool.rec (.add k' v' (p.insert_k k v))
        (Bool.rec (.add (Int.add_k k k') v' p) p (Int.beqZero_k (Int.add_k k k')))
        (Nat.beq v v'))
      (.add k v (.add k' v' p))
      (Nat.blt v' v) = _
    have hz : (Int.add k k' == 0) = Int.beqZero_k (Int.add_k k k') := by rw [Int.beqZero_k_eq, Int.add_k_eq]
    show _ = (bif Nat.blt v' v then .add k v (.add k' v' p) else bif Nat.beq v v' then
      (if (Int.add k k' == 0) = true then p else .add (Int.add k k') v' p) else .add k' v' (p.insert k v))
    rw [ih, hz, show Int.add k k' = Int.add_k k k' by rw [Int.add_k_eq]]
    cases Nat.blt v' v <;> cases Nat.beq v v' <;> cases Int.beqZero_k (Int.add_k k k') <;> rfl

noncomputable def Poly.norm_k (p : Poly) : Poly :=
  Poly.rec .nil (fun k v _ ih => ih.insert_k k v) p

@[simp] theorem Poly.norm_k_eq (p : Poly) : p.norm_k = p.norm := by
  induction p with
  | nil => rfl
  | add k v p ih => show (p.norm_k).insert_k k v = _; rw [ih, insert_k_eq]; rfl

noncomputable def Expr.toPoly'_k (e : Expr) : Poly :=
  Expr.rec (motive := fun _ => Int → Poly → Poly)
    (fun _ p => p)
    (fun v c p => .add c v p)
    (fun _ _ iha ihb c p => iha c (ihb c p))
    (fun _ _ iha ihb c p => iha c (ihb (Int.neg_k c) p))
    (fun _ iha c p => iha (Int.neg_k c) p)
    (fun k _ iha c p => Bool.rec (iha (Int.mul_k c (Int.ofNat k)) p) p (Nat.beq k 0))
    (fun k _ iha c p => Bool.rec (iha (Int.mul_k c k) p) p (Int.beqZero_k k))
    e 1 .nil

theorem Expr.toPoly'_k_go (e : Expr) (c : Int) (p : Poly) :
    Expr.rec (motive := fun _ => Int → Poly → Poly)
      (fun _ p => p)
      (fun v c p => .add c v p)
      (fun _ _ iha ihb c p => iha c (ihb c p))
      (fun _ _ iha ihb c p => iha c (ihb (Int.neg_k c) p))
      (fun _ iha c p => iha (Int.neg_k c) p)
      (fun k _ iha c p => Bool.rec (iha (Int.mul_k c (Int.ofNat k)) p) p (Nat.beq k 0))
      (fun k _ iha c p => Bool.rec (iha (Int.mul_k c k) p) p (Int.beqZero_k k))
      e c p = toPoly'.go c e p := by
  induction e generalizing c p with
  | zero => rfl
  | var v => rfl
  | add a b iha ihb => simp only [toPoly'.go, Function.comp_apply]; rw [iha, ihb]
  | sub a b iha ihb => simp only [toPoly'.go, Function.comp_apply]; rw [iha, ihb, Int.neg_k_eq]; rfl
  | neg a ih => simp only [toPoly'.go]; rw [ih, Int.neg_k_eq]; rfl
  | natMul k a ih =>
    simp only [toPoly'.go]
    rw [show (k == 0) = Nat.beq k 0 from rfl]
    cases Nat.beq k 0
    · simp only [Bool.cond_false]; rw [← ih, Int.mul_k_eq]; rfl
    · simp only [Bool.cond_true]; rfl
  | intMul k a ih =>
    simp only [toPoly'.go]
    rw [← Int.beqZero_k_eq]
    cases Int.beqZero_k k
    · simp only [Bool.cond_false]; rw [← ih, Int.mul_k_eq]
    · simp only [Bool.cond_true]; rfl

noncomputable def Expr.norm_k (e : Expr) : Poly :=
  e.toPoly'_k.norm_k

@[simp] theorem Expr.norm_k_eq (e : Expr) : e.norm_k = e.norm := by
  unfold norm_k norm toPoly'_k toPoly'; rw [Poly.norm_k_eq, Expr.toPoly'_k_go]

noncomputable def eq_norm_cert (lhs rhs : Expr) : Bool :=
  lhs.norm_k.beq' rhs.norm_k

theorem eq_of_norm_eq {α} [IntModule α] (ctx : Context α) (lhs rhs : Expr)
    : eq_norm_cert lhs rhs → lhs.denote_k ctx = rhs.denote_k ctx := by
  simp only [eq_norm_cert, Poly.beq'_eq, Expr.norm_k_eq, Expr.denote_k_eq_denote]
  intro h
  have h := congrArg (Poly.denote ctx) h
  simpa only [Expr.denote_norm] using h

def Poly.leadCoeff (p : Poly) : Int :=
  match p with
  | .add a _ _ => a
  | _ => 1

open OrderedAdd

/-!
Helper theorems for conflict resolution during model construction.
-/

private theorem le_add_le {α} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] {a b : α}
    (h₁ : a ≤ 0) (h₂ : b ≤ 0) : a + b ≤ 0 := by
  replace h₁ := add_le_left h₁ b; simp at h₁
  exact le_trans h₁ h₂

private theorem le_add_lt {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α}
    (h₁ : a ≤ 0) (h₂ : b < 0) : a + b < 0 := by
  replace h₁ := add_le_left h₁ b; simp at h₁
  exact Preorder.lt_of_le_of_lt h₁ h₂

private theorem lt_add_lt {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] {a b : α}
    (h₁ : a < 0) (h₂ : b < 0) : a + b < 0 := by
  replace h₁ := add_lt_left h₁ b; simp at h₁
  exact Preorder.lt_trans h₁ h₂

private theorem coe_natAbs_nonneg (a : Int) : (a.natAbs : Int) ≥ 0 := by
  exact Int.natCast_nonneg a.natAbs

noncomputable def le_le_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  p₃.beq' (p₁.mul_k a₂ |>.combine_k (p₂.mul_k a₁))

theorem le_le_combine {α} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : le_le_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx ≤ 0 → p₃.denote' ctx ≤ 0 := by
  simp [le_le_combine_cert]; intro _ h₁ h₂; subst p₃; simp
  replace h₁ := zsmul_nonpos (coe_natAbs_nonneg p₂.leadCoeff) h₁
  replace h₂ := zsmul_nonpos (coe_natAbs_nonneg p₁.leadCoeff) h₂
  exact le_add_le h₁ h₂

noncomputable def le_lt_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  a₁ > (0 : Int) && p₃.beq' (p₁.mul_k a₂ |>.combine_k (p₂.mul_k a₁))

theorem le_lt_combine {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : le_lt_combine_cert p₁ p₂ p₃ → p₁.denote' ctx ≤ 0 → p₂.denote' ctx < 0 → p₃.denote' ctx < 0 := by
  simp [-Int.natAbs_pos, -Int.natCast_pos, le_lt_combine_cert]; intro hp _ h₁ h₂; subst p₃; simp
  replace h₁ := zsmul_nonpos (coe_natAbs_nonneg p₂.leadCoeff) h₁
  replace h₂ := zsmul_neg_iff (↑p₁.leadCoeff.natAbs) h₂ |>.mpr hp
  exact le_add_lt h₁ h₂

noncomputable def lt_lt_combine_cert (p₁ p₂ p₃ : Poly) : Bool :=
  let a₁ := p₁.leadCoeff.natAbs
  let a₂ := p₂.leadCoeff.natAbs
  a₂ > (0 : Int) && a₁ > (0 : Int) && p₃.beq' (p₁.mul_k a₂ |>.combine_k (p₂.mul_k a₁))

theorem lt_lt_combine {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (p₁ p₂ p₃ : Poly)
    : lt_lt_combine_cert p₁ p₂ p₃ → p₁.denote' ctx < 0 → p₂.denote' ctx < 0 → p₃.denote' ctx < 0 := by
  simp [-Int.natAbs_pos, -Int.natCast_pos, lt_lt_combine_cert]; intro hp₁ hp₂ _ h₁ h₂; subst p₃; simp
  replace h₁ := zsmul_neg_iff (↑p₂.leadCoeff.natAbs) h₁ |>.mpr hp₁
  replace h₂ := zsmul_neg_iff (↑p₁.leadCoeff.natAbs) h₂ |>.mpr hp₂
  exact lt_add_lt h₁ h₂

noncomputable def diseq_split_cert (p₁ p₂ : Poly) : Bool :=
  p₂.beq' (p₁.mul_k (-1))

-- We need `LinearOrder` to use `trichotomy`
theorem diseq_split {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (ctx : Context α) (p₁ p₂ : Poly)
    : diseq_split_cert p₁ p₂ → p₁.denote' ctx ≠ 0 → p₁.denote' ctx < 0 ∨ p₂.denote' ctx < 0 := by
  simp [diseq_split_cert]; intro _ h₁; subst p₂; simp
  cases LinearOrder.trichotomy (p₁.denote ctx) 0
  next h => exact Or.inl h
  next h =>
    apply Or.inr
    simp [h₁] at h
    rw [← neg_pos_iff, neg_zsmul, neg_neg, one_zsmul]; assumption

theorem diseq_split_resolve {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (ctx : Context α) (p₁ p₂ : Poly)
    : diseq_split_cert p₁ p₂ → p₁.denote' ctx ≠ 0 → ¬p₁.denote' ctx < 0 → p₂.denote' ctx < 0 := by
  intro h₁ h₂ h₃
  exact (diseq_split ctx p₁ p₂ h₁ h₂).resolve_left h₃

/-!
Helper theorems for internalizing facts into the linear arithmetic procedure
-/

noncomputable def norm_cert (lhs rhs : Expr) (p : Poly) :=
  p.beq' (lhs.sub rhs).norm_k

theorem eq_norm {α} [IntModule α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote_k ctx = rhs.denote_k ctx → p.denote' ctx = 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]

theorem le_of_eq {α} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote_k ctx = rhs.denote_k ctx → p.denote' ctx ≤ 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote, h₁, sub_self]

theorem diseq_norm {α} [IntModule α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote_k ctx ≠ rhs.denote_k ctx → p.denote' ctx ≠ 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote]
  intro h
  replace h := congrArg (rhs.denote ctx + ·) h; simp [sub_eq_add_neg] at h
  rw [add_left_comm, ← sub_eq_add_neg, sub_self, add_zero] at h
  contradiction

theorem le_norm {α} [IntModule α] [LE α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote_k ctx ≤ rhs.denote_k ctx → p.denote' ctx ≤ 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote]
  replace h₁ := add_le_left h₁ (-rhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem lt_norm {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedAdd α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert lhs rhs p → lhs.denote_k ctx < rhs.denote_k ctx → p.denote' ctx < 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote]
  replace h₁ := add_lt_left h₁ (-rhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_le_norm {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert rhs lhs p → ¬ lhs.denote_k ctx ≤ rhs.denote_k ctx → p.denote' ctx < 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote]
  replace h₁ := LinearOrder.lt_of_not_le h₁
  replace h₁ := add_lt_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

theorem not_lt_norm {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (ctx : Context α) (lhs rhs : Expr) (p : Poly)
    : norm_cert rhs lhs p → ¬ lhs.denote_k ctx < rhs.denote_k ctx → p.denote' ctx ≤ 0 := by
  simp only [Expr.denote_k_eq_denote]; simp [norm_cert]; intro _ h₁; subst p; simp [Expr.denote]
  replace h₁ := LinearOrder.le_of_not_lt h₁
  replace h₁ := add_le_left h₁ (-lhs.denote ctx)
  simp [← sub_eq_add_neg, sub_self] at h₁
  assumption

/-!
Helper theorems for closing the goal
-/

theorem diseq_unsat {α} [IntModule α] (ctx : Context α) : (Poly.nil).denote ctx ≠ 0 → False := by
  simp [Poly.denote]

theorem lt_unsat {α} [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] (ctx : Context α) : (Poly.nil).denote ctx < 0 → False := by
  simp [Poly.denote]; intro h
  have := lt_iff_le_and_not_ge.mp h
  simp at this

noncomputable def zero_lt_one_cert (p : Poly) : Bool :=
  p.beq' (.add (-1) 0 .nil)

theorem zero_lt_one {α} [Ring α] [LE α] [LT α] [LawfulOrderLT α] [IsPreorder α] [OrderedRing α] (ctx : Context α) (p : Poly)
    : zero_lt_one_cert p → (0 : Var).denote ctx = One.one → p.denote' ctx < 0 := by
  simp [zero_lt_one_cert]; intro _ h; subst p; simp [Poly.denote, h, One.one, neg_zsmul]
  rw [neg_lt_iff, neg_zero]; apply OrderedRing.zero_lt_one

/-!
Coefficient normalization
-/

noncomputable def eq_neg_cert (p₁ p₂ : Poly) :=
  p₂.beq' (p₁.mul_k (-1))

theorem eq_neg {α} [IntModule α] (ctx : Context α) (p₁ p₂ : Poly)
    : eq_neg_cert p₁ p₂ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp [eq_neg_cert]; intros; simp [*]

noncomputable def eq_coeff_cert (p₁ p₂ : Poly) (k : Nat) :=
  k != 0 && p₁.beq' (p₂.mul_k k)

theorem eq_coeff {α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α) (p₁ p₂ : Poly) (k : Nat)
    : eq_coeff_cert p₁ p₂ k → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 := by
  simp [eq_coeff_cert]; intro h _; subst p₁; simp [*, zsmul_natCast_eq_nsmul]
  exact NoNatZeroDivisors.eq_zero_of_mul_eq_zero h

theorem diseq_neg {α} [IntModule α] (ctx : Context α) (p p' : Poly) : p'.beq' (p.mul_k (-1)) → p.denote' ctx ≠ 0 → p'.denote' ctx ≠ 0 := by
  simp; intro _ _; subst p'; simp [neg_zsmul]
  intro h; replace h := congrArg (- ·) h; simp [neg_neg, neg_zero] at h
  contradiction

/-!
Substitution
-/

noncomputable def eq_diseq_subst_cert (k₁ k₂ : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  k₁.natAbs ≠ 0 && p₃.beq' (p₁.mul_k k₂ |>.combine_k (p₂.mul_k k₁))

theorem eq_diseq_subst {α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α) (k₁ k₂ : Int) (p₁ p₂ p₃ : Poly)
    : eq_diseq_subst_cert k₁ k₂ p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [eq_diseq_subst_cert, - Int.natAbs_eq_zero, -Int.natCast_eq_zero]; intro hne _ h₁ h₂; subst p₃
  simp [h₁]; intro h₃
  have :  k₁.natAbs • Poly.denote ctx p₂ = 0 := by
    have : (k₁.natAbs : Int) • Poly.denote ctx p₂ = 0 := by
      cases Int.natAbs_eq_iff.mp (Eq.refl k₁.natAbs)
      next h => rw [← h]; assumption
      next h => replace h := congrArg (- ·) h; simp at h; rw [← h, neg_zsmul, h₃, neg_zero]
    simpa [zsmul_natCast_eq_nsmul] using this
  have := NoNatZeroDivisors.eq_zero_of_mul_eq_zero hne this
  contradiction

noncomputable def eq_diseq_subst1_cert (k : Int) (p₁ p₂ p₃ : Poly) : Bool :=
  p₃.beq' (p₁.mul_k k |>.combine_k p₂)

/-
Special case of `diseq_eq_subst` where leading coefficient `c₁` of `p₁` is `-k*c₂`, where
`c₂` is the leading coefficient of `p₂`.
-/
theorem eq_diseq_subst1 {α} [IntModule α] (ctx : Context α) (k : Int) (p₁ p₂ p₃ : Poly)
    : eq_diseq_subst1_cert k p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx ≠ 0 → p₃.denote' ctx ≠ 0 := by
  simp [eq_diseq_subst1_cert]; intro _ h₁ h₂; subst p₃
  simp [h₁, h₂]

noncomputable def eq_eq_subst_cert (x : Var) (p₁ p₂ p₃ : Poly) :=
  let a := p₁.coeff_k x
  let b := p₂.coeff_k x
  p₃.beq' (p₂.mul_k a |>.combine_k (p₁.mul_k (Int.neg_k b)))

theorem eq_eq_subst {α} [IntModule α] (ctx : Context α) (x : Var) (p₁ p₂ p₃ : Poly)
    : eq_eq_subst_cert x p₁ p₂ p₃ → p₁.denote' ctx = 0 → p₂.denote' ctx = 0 → p₃.denote' ctx = 0 := by
  simp [eq_eq_subst_cert]; intro _ h₁ h₂; subst p₃; simp [h₁, h₂]

noncomputable def imp_eq_cert (p : Poly) (x y : Var) : Bool :=
  p.beq' (.add 1 x (.add (-1) y .nil))

theorem imp_eq {α} [IntModule α] (ctx : Context α) (p : Poly) (x y : Var)
    : imp_eq_cert p x y → p.denote' ctx = 0 → x.denote ctx = y.denote ctx := by
  simp [imp_eq_cert]; intro; subst p; simp [Poly.denote]
  rw [neg_zsmul, ← sub_eq_add_neg, one_zsmul, sub_eq_zero_iff]
  simp

end Lean.Grind.Linarith
