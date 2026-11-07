/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.RArray
import Init.LawfulBEqTactics
import Init.ByCases
import Init.Data.Prod
import Init.Data.Bool

public section

@[expose] section

namespace Nat.Internal.Linear

/-!
  Helper definitions and theorems for constructing linear arithmetic proofs.
-/

abbrev Var := Nat

abbrev Context := Lean.RArray Nat

/--
  When encoding polynomials. We use `fixedVar` for encoding numerals.
  The denotation of `fixedVar` is always `1`. -/
abbrev fixedVar := 100000000 -- Any big number should work here

noncomputable abbrev Var.denote (ctx : Context) (v : Var) : Nat :=
  Bool.rec (ctx.get v) 1 (Nat.beq v fixedVar)

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited, BEq

noncomputable abbrev Expr.denote (ctx : Context) : Expr → Nat
  | .add a b  => Nat.add (denote ctx a) (denote ctx b)
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => Nat.mul k (denote ctx e)
  | .mulR e k => Nat.mul (denote ctx e) k

abbrev Poly := List (Nat × Var)

noncomputable abbrev Poly.denote (ctx : Context) (p : Poly) : Nat :=
  match p with
  | [] => 0
  | (k, v) :: p => Nat.add (Nat.mul k (v.denote ctx)) (denote ctx p)

def Poly.insert (k : Nat) (v : Var) (p : Poly) : Poly :=
  match p with
  | [] => [(k, v)]
  | (k', v') :: p =>
    bif Nat.blt v v' then
      (k, v) :: (k', v') :: p
    else bif Nat.beq v v' then
      (k + k', v') :: p
    else
      (k', v') :: insert k v p

def Poly.norm (p : Poly) : Poly := go p []
where
  go (p : Poly) (r : Poly) : Poly :=
    match p with
    | [] => r
    | (k, v) :: p => go p (r.insert k v)

def Poly.cancelAux (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly) : Poly × Poly :=
  match fuel with
  | 0 => (r₁.reverse ++ m₁, r₂.reverse ++ m₂)
  | fuel + 1 =>
    match m₁, m₂ with
    | m₁, [] => (r₁.reverse ++ m₁, r₂.reverse)
    | [], m₂ => (r₁.reverse, r₂.reverse ++ m₂)
    | (k₁, v₁) :: m₁, (k₂, v₂) :: m₂ =>
      bif Nat.blt v₁ v₂ then
        cancelAux fuel m₁ ((k₂, v₂) :: m₂) ((k₁, v₁) :: r₁) r₂
      else bif Nat.blt v₂ v₁ then
        cancelAux fuel ((k₁, v₁) :: m₁) m₂ r₁ ((k₂, v₂) :: r₂)
      else bif Nat.blt k₁ k₂ then
        cancelAux fuel m₁ m₂ r₁ ((Nat.sub k₂ k₁, v₁) :: r₂)
      else bif Nat.blt k₂ k₁ then
        cancelAux fuel m₁ m₂ ((Nat.sub k₁ k₂, v₁) :: r₁) r₂
      else
        cancelAux fuel m₁ m₂ r₁ r₂

def hugeFuel := 1000000 -- any big number should work

def Poly.cancel (p₁ p₂ : Poly) : Poly × Poly :=
  cancelAux hugeFuel p₁ p₂ [] []

def Poly.isNum? (p : Poly) : Option Nat :=
  match p with
  | [] => some 0
  | [(k, v)] => bif v == fixedVar then some k else none
  | _ => none

def Poly.isZero (p : Poly) : Bool :=
  match p with
  | [] => true
  | _  => false

def Poly.isNonZero (p : Poly) : Bool :=
  match p with
  | [] => false
  | (k, v) :: p => bif v == fixedVar then k > 0 else isNonZero p

abbrev Poly.denote_eq (ctx : Context) (mp : Poly × Poly) : Prop :=
  mp.1.denote ctx = mp.2.denote ctx

abbrev Poly.denote_le (ctx : Context) (mp : Poly × Poly) : Prop :=
  mp.1.denote ctx ≤ mp.2.denote ctx

set_option allowUnsafeReducibility true
attribute [semireducible] Poly.denote_eq Poly.denote_le

def Expr.toPoly (e : Expr) :=
  go 1 e []
where
  -- Implementation note: This assembles the result using difference lists
  -- to avoid `++` on lists.
  go (coeff : Nat) : Expr → (Poly → Poly)
    | .num k    => bif k == 0 then id else ((coeff * k, fixedVar) :: ·)
    | .var i    => ((coeff, i) :: ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .mulL k a
    | .mulR a k => bif k == 0 then id else go (coeff * k) a

def Expr.toNormPoly (e : Expr) : Poly :=
  e.toPoly.norm

def Expr.inc (e : Expr) : Expr :=
   .add e (.num 1)

structure PolyCnstr  where
  eq  : Bool
  lhs : Poly
  rhs : Poly
  deriving BEq, ReflBEq, LawfulBEq

structure ExprCnstr where
  eq  : Bool
  lhs : Expr
  rhs : Expr

abbrev PolyCnstr.denote (ctx : Context) (c : PolyCnstr) : Prop :=
  bif c.eq then
    Poly.denote_eq ctx (c.lhs, c.rhs)
  else
    Poly.denote_le ctx (c.lhs, c.rhs)

def PolyCnstr.norm (c : PolyCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.norm c.rhs.norm
  { eq := c.eq, lhs, rhs }

def PolyCnstr.isUnsat (c : PolyCnstr) : Bool :=
  bif c.eq then
    (c.lhs.isZero && c.rhs.isNonZero) || (c.lhs.isNonZero && c.rhs.isZero)
  else
    c.lhs.isNonZero && c.rhs.isZero

def PolyCnstr.isValid (c : PolyCnstr) : Bool :=
  bif c.eq then
    c.lhs.isZero && c.rhs.isZero
  else
    c.lhs.isZero

abbrev ExprCnstr.denote (ctx : Context) (c : ExprCnstr) : Prop :=
  bif c.eq then
    c.lhs.denote ctx = c.rhs.denote ctx
  else
    c.lhs.denote ctx ≤ c.rhs.denote ctx

def ExprCnstr.toPoly (c : ExprCnstr) : PolyCnstr :=
  { c with lhs := c.lhs.toPoly, rhs := c.rhs.toPoly }

def ExprCnstr.toNormPoly (c : ExprCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.toNormPoly c.rhs.toNormPoly
  { c with lhs, rhs }

def monomialToExpr (k : Nat) (v : Var) : Expr :=
  bif v == fixedVar then
    .num k
  else bif k == 1 then
    .var v
  else
    .mulL k (.var v)

def Poly.toExpr (p : Poly) : Expr :=
  match p with
  | [] => .num 0
  | (k, v) :: p => go (monomialToExpr k v) p
where
  go (e : Expr) (p : Poly) : Expr :=
    match p with
    | [] => e
    | (k, v) :: p => go (.add e (monomialToExpr k v)) p

def PolyCnstr.toExpr (c : PolyCnstr) : ExprCnstr :=
  { c with lhs := c.lhs.toExpr, rhs := c.rhs.toExpr }

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.right_distrib Nat.left_distrib Nat.mul_assoc Nat.mul_comm
attribute [local simp] Poly.denote Expr.denote Poly.insert Poly.norm Poly.norm.go Poly.cancelAux

theorem Poly.denote_insert (ctx : Context) (k : Nat) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  match p with
  | [] => simp
  | (k', v') :: p =>
    by_cases h₁ : Nat.blt v v'
    · simp [h₁]
    · by_cases h₂ : Nat.beq v v'
      · simp only [insert, h₁, h₂, Bool.cond_false, Bool.cond_true]
        simp [Nat.eq_of_beq_eq_true h₂]
      · simp only [insert, h₁, h₂, Bool.cond_false]
        simp [denote_insert]

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm_go (ctx : Context) (p : Poly) (r : Poly) : (norm.go p r).denote ctx = p.denote ctx + r.denote ctx := by
  match p with
  | [] => simp
  | (k, v):: p => simp [denote_norm_go]

attribute [local simp] Poly.denote_norm_go

theorem Poly.denote_sort (ctx : Context) (m : Poly) : m.norm.denote ctx = m.denote ctx := by
  simp

attribute [local simp] Poly.denote_sort

theorem Poly.denote_append (ctx : Context) (p q : Poly) : (p ++ q).denote ctx = p.denote ctx + q.denote ctx := by
  match p with
  | []  => simp
  | (k, v) :: p => simp [denote_append]

attribute [local simp] Poly.denote_append

theorem Poly.denote_cons (ctx : Context) (k : Nat) (v : Var) (p : Poly) : denote ctx ((k, v) :: p) = k * v.denote ctx + p.denote ctx := by
  match p with
  | []     => simp
  | _ :: m => simp

attribute [local simp] Poly.denote_cons

theorem Poly.denote_reverse (ctx : Context) (p : Poly) : denote ctx (List.reverse p) = denote ctx p := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_reverse

private theorem eq_of_not_blt_eq_true (h₁ : ¬ (Nat.blt x y = true)) (h₂ : ¬ (Nat.blt y x = true)) : x = y :=
  have h₁ : ¬ x < y := fun h => h₁ (Nat.blt_eq.mpr h)
  have h₂ : ¬ y < x := fun h => h₂ (Nat.blt_eq.mpr h)
  Nat.le_antisymm (Nat.ge_of_not_lt h₂) (Nat.ge_of_not_lt h₁)

theorem Poly.denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp
    split <;> try (simp at h; try assumption)
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [Nat.blt_eq ▸ hltv]
    · apply ih; simp [denote_eq] at h |-; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [Nat.blt_eq ▸ hgtv]
      · apply ih; simp [denote_eq] at h |-; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [Nat.blt_eq ▸ hltk]
        · apply ih
          simp [denote_eq] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Eq.symm
          apply Nat.sub_eq_of_eq_add
          simp [h]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [Nat.blt_eq ▸ hgtk]
          · apply ih
            simp [denote_eq] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hgtk))
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_eq_of_eq_add
            simp [h]
          · have heqk : k₁ = k₂ := eq_of_not_blt_eq_true hltk hgtk; subst heqk
            apply ih
            simp [denote_eq] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            exact Nat.add_right_cancel h

theorem Poly.of_denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp at h
    split at h <;> (try simp; assumption)
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [Nat.blt_eq ▸ hltv] at h
    · have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [Nat.blt_eq ▸ hgtv] at h
      · have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [Nat.blt_eq ▸ hltk] at h
        · have ih := ih (h := h); simp [denote_eq] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih.symm
          simp at ih
          rw [ih]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [Nat.blt_eq ▸ hgtk] at h
          · have ih := ih (h := h); simp [denote_eq] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hgtk))
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at ih
            rw [ih]
          · have heqk : k₁ = k₂ := eq_of_not_blt_eq_true hltk hgtk; subst heqk
            have ih := ih (h := h); simp [denote_eq] at ih ⊢
            rw [← Nat.add_assoc, ih, Nat.add_assoc]

theorem Poly.denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (m₁, m₂)) : denote_eq ctx (cancel m₁ m₂) := by
  apply denote_eq_cancelAux; simp [h]

theorem Poly.of_denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (cancel m₁ m₂)) : denote_eq ctx (m₁, m₂) := by
  have := Poly.of_denote_eq_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_eq_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_eq ctx (cancel m₁ m₂) = denote_eq ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_eq_cancel h) (fun h => denote_eq_cancel h)

attribute [local simp] Poly.denote_eq_cancel_eq

theorem Poly.denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp
    split <;> try (simp at h; assumption)
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [Nat.blt_eq ▸ hltv]
    · apply ih; simp [denote_le] at h |-; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [Nat.blt_eq ▸ hgtv]
      · apply ih; simp [denote_le] at h |-; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [Nat.blt_eq ▸ hltk]
        · apply ih
          simp [denote_le] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Nat.le_sub_of_add_le
          simp [h]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [Nat.blt_eq ▸ hgtk]
          · apply ih
            simp [denote_le] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hgtk))
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_le_of_le_add
            simp [h]
          · have heqk : k₁ = k₂ := eq_of_not_blt_eq_true hltk hgtk; subst heqk
            apply ih
            simp [denote_le] at h |-
            rw [← Nat.add_assoc, ← Nat.add_assoc] at h
            apply Nat.le_of_add_le_add_right h
    done

theorem Poly.of_denote_le_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_le ctx (cancelAux fuel m₁ m₂ r₁ r₂)) : denote_le ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp at h
    split at h <;> try (simp; assumption)
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [Nat.blt_eq ▸ hltv] at h
    · have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [Nat.blt_eq ▸ hgtv] at h
      · have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [Nat.blt_eq ▸ hltk] at h
        · have ih := ih (h := h); simp [denote_le] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have := Nat.add_le_of_le_sub (Nat.le_trans haux (Nat.le_add_left ..)) ih
          simp at this
          exact this
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [Nat.blt_eq ▸ hgtk] at h
          · have ih := ih (h := h); simp [denote_le] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hgtk))
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have := Nat.le_add_of_sub_le ih
            simp at this
            exact this
          · have heqk : k₁ = k₂ := eq_of_not_blt_eq_true hltk hgtk; subst heqk
            have ih := ih (h := h); simp [denote_le] at ih ⊢
            have := Nat.add_le_add_right ih (k₁ * Var.denote ctx v₁)
            simp at this
            exact this

theorem Poly.denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (m₁, m₂)) : denote_le ctx (cancel m₁ m₂) := by
  apply denote_le_cancelAux; simp [h]

theorem Poly.of_denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (cancel m₁ m₂)) : denote_le ctx (m₁, m₂) := by
  have := Poly.of_denote_le_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_le_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_le ctx (cancel m₁ m₂) = denote_le ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_le_cancel h) (fun h => denote_le_cancel h)

attribute [local simp] Poly.denote_le_cancel_eq

theorem Expr.denote_toPoly_go (ctx : Context) (e : Expr) :
  (toPoly.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
  induction k, e using Expr.toPoly.go.induct generalizing p with
  | case1 k k' h =>
    simp [toPoly.go, eq_of_beq h]
  | case2 k k' h =>
    simp [toPoly.go, h, Var.denote]
  | case3 k i => simp [toPoly.go]
  | case4 k a b iha ihb => simp [toPoly.go, iha, ihb]
  | case5 k k' a h => simp [toPoly.go, eq_of_beq h]
  | case6 k a k' h ih =>
    simp only [toPoly.go, denote, mul_eq]
    simp [h, ih, Nat.mul_assoc]
  | case7 k a k' h =>
    simp only [toPoly.go, denote, mul_eq]
    simp [eq_of_beq h]
  | case8 k a k' h ih =>
    simp only [toPoly.go, denote, mul_eq]
    simp [h, ih, Nat.mul_assoc]

theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  simp [toPoly, Expr.denote_toPoly_go]

attribute [local simp] Expr.denote_toPoly

theorem Expr.eq_of_toNormPoly (ctx : Context) (a b : Expr) (h : a.toNormPoly = b.toNormPoly) : a.denote ctx = b.denote ctx := by
  simp [toNormPoly, Poly.norm] at h
  have h := congrArg (Poly.denote ctx) h
  simp at h
  assumption

theorem Expr.of_cancel_eq (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) := by
  have := Poly.denote_eq_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.norm, Poly.denote_eq, -eq_iff_iff] at this
  exact this.symm

theorem Expr.of_cancel_le (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx ≤ b.denote ctx) = (c.denote ctx ≤ d.denote ctx) := by
  have := Poly.denote_le_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.norm,Poly.denote_le, -eq_iff_iff] at this
  exact this.symm

theorem Expr.of_cancel_lt (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.inc.toNormPoly b.toNormPoly = (c.inc.toPoly, d.toPoly)) : (a.denote ctx < b.denote ctx) = (c.denote ctx < d.denote ctx) :=
  of_cancel_le ctx a.inc b c.inc d h

theorem ExprCnstr.denote_toPoly (ctx : Context) (c : ExprCnstr) : c.toPoly.denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  simp [ExprCnstr.denote, PolyCnstr.denote, ExprCnstr.toPoly];
  by_cases h : eq = true <;> simp [h]
  · simp [Poly.denote_eq]
  · simp [Poly.denote_le]

attribute [local simp] ExprCnstr.denote_toPoly

theorem ExprCnstr.denote_toNormPoly (ctx : Context) (c : ExprCnstr) : c.toNormPoly.denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  simp [ExprCnstr.denote, PolyCnstr.denote, ExprCnstr.toNormPoly]
  by_cases h : eq = true <;> simp [h]
  · rw [Poly.denote_eq_cancel_eq]; simp [Poly.denote_eq, Expr.toNormPoly, Poly.norm]
  · rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_le, Expr.toNormPoly, Poly.norm]

attribute [local simp] ExprCnstr.denote_toNormPoly

theorem Poly.of_isZero (ctx : Context) {p : Poly} (h : isZero p = true) : p.denote ctx = 0 := by
  simp [isZero] at h
  split at h
  · simp
  · contradiction

theorem Poly.of_isNonZero (ctx : Context) {p : Poly} (h : isNonZero p = true) : p.denote ctx > 0 := by
  match p with
  | [] => contradiction
  | (k, v) :: p =>
    by_cases he : v == fixedVar <;> simp [he, isNonZero] at h ⊢
    · simp [eq_of_beq he, Var.denote]; apply Nat.lt_of_succ_le; exact Nat.le_trans h (Nat.le_add_right ..)
    · have ih := of_isNonZero ctx h
      exact Nat.le_trans ih (Nat.le_add_right ..)

theorem PolyCnstr.eq_false_of_isUnsat (ctx : Context) {c : PolyCnstr} : c.isUnsat → c.denote ctx = False := by
  cases c; rename_i eq lhs rhs
  simp [isUnsat]
  by_cases he : eq = true <;> simp [he, Poly.denote_eq, Poly.denote_le, -and_imp]
  · intro
      | Or.inl ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₁]; have := Nat.ne_zero_of_lt (Poly.of_isNonZero ctx h₂); simp [this.symm]
      | Or.inr ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₂]; have := Nat.ne_zero_of_lt (Poly.of_isNonZero ctx h₁); simp [this]
  · intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₂]
    exact Poly.of_isNonZero ctx h₁

theorem PolyCnstr.eq_true_of_isValid (ctx : Context) {c : PolyCnstr} : c.isValid → c.denote ctx = True := by
  cases c; rename_i eq lhs rhs
  simp [isValid]
  by_cases he : eq = true <;> simp [he, Poly.denote_eq, Poly.denote_le, -and_imp]
  · intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₁, h₂]
  · intro h
    simp [Poly.of_isZero, h]

theorem ExprCnstr.eq_false_of_isUnsat (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isUnsat) : c.denote ctx = False := by
  have := PolyCnstr.eq_false_of_isUnsat ctx h
  rwa [denote_toNormPoly] at this

theorem ExprCnstr.eq_true_of_isValid (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isValid) : c.denote ctx = True := by
  have := PolyCnstr.eq_true_of_isValid ctx h
  rwa [denote_toNormPoly] at this

theorem ExprCnstr.eq_of_toNormPoly_eq (ctx : Context) (c d : ExprCnstr) (h : c.toNormPoly == d.toPoly) : c.denote ctx = d.denote ctx := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rwa [denote_toNormPoly, denote_toPoly] at h

theorem Expr.eq_of_toNormPoly_eq (ctx : Context) (e e' : Expr) (h : e.toNormPoly == e'.toPoly) : e.denote ctx = e'.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Expr.toNormPoly, Poly.norm] at h
  assumption

/-! Kernel-reduction variants for the certificates of `simp +arith` over `Nat`. -/

noncomputable def Expr.denote_k (ctx : Context) (e : Expr) : Nat :=
  Expr.rec (fun k => k) (fun v => v.denote ctx) (fun _ _ a b => Nat.add a b) (fun k _ a => Nat.mul k a)
    (fun _ k a => Nat.mul a k) e

theorem Expr.denote_k_eq_denote (ctx : Context) (e : Expr) : e.denote_k ctx = e.denote ctx := by
  induction e with
  | num => rfl
  | var => rfl
  | add a b iha ihb => show Nat.add (a.denote_k ctx) (b.denote_k ctx) = _; rw [iha, ihb]
  | mulL k a ih => show Nat.mul k (a.denote_k ctx) = _; rw [ih]
  | mulR a k ih => show Nat.mul (a.denote_k ctx) k = _; rw [ih]

noncomputable def ExprCnstr.denote_k (ctx : Context) (c : ExprCnstr) : Prop :=
  Bool.rec (c.lhs.denote_k ctx ≤ c.rhs.denote_k ctx) (c.lhs.denote_k ctx = c.rhs.denote_k ctx) c.eq

theorem ExprCnstr.denote_k_eq_denote (ctx : Context) (c : ExprCnstr) : c.denote_k ctx = c.denote ctx := by
  cases c with
  | mk eq lhs rhs => cases eq <;> simp [denote_k, denote, Expr.denote_k_eq_denote]

noncomputable def Poly.insert_k (k : Nat) (v : Var) (p : Poly) : Poly :=
  List.rec [(k, v)]
    (fun hd tl ih => Bool.rec (Bool.rec (hd :: ih) ((Nat.add k hd.1, hd.2) :: tl) (Nat.beq v hd.2)) ((k, v) :: hd :: tl) (Nat.blt v hd.2))
    p

theorem Poly.insert_k_eq (k : Nat) (v : Var) (p : Poly) : p.insert_k k v = p.insert k v := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    cases hd; rename_i k' v'
    show Bool.rec (motive := fun _ => Poly) (Bool.rec (motive := fun _ => Poly) ((k', v') :: Poly.insert_k k v tl) _ _) _ (Nat.blt v v') = _
    rw [ih]; simp only [Poly.insert]
    cases Nat.blt v v' <;> cases Nat.beq v v' <;> rfl

noncomputable def Poly.norm_k (p : Poly) : Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun r => r) (fun hd _ ih r => ih (r.insert_k hd.1 hd.2)) p []

theorem Poly.norm_k_eq (p : Poly) : p.norm_k = p.norm := by
  suffices h : ∀ r, List.rec (motive := fun _ => Poly → Poly) (fun r => r) (fun hd _ ih r => ih (r.insert_k hd.1 hd.2)) p r
      = Poly.norm.go p r by exact h []
  induction p with
  | nil => intro r; rfl
  | cons hd tl ih =>
    intro r; cases hd; rename_i k v
    show List.rec (motive := fun _ => Poly → Poly) _ _ tl _ = _; rw [ih, Poly.insert_k_eq]; rfl

noncomputable def Poly.append_k (p q : Poly) : Poly :=
  List.rec q (fun hd _ ih => hd :: ih) p

theorem Poly.append_k_eq (p q : Poly) : p.append_k q = p ++ q := by
  induction p with
  | nil => rfl
  | cons hd tl ih => show hd :: Poly.append_k tl q = _; rw [ih]; rfl

noncomputable def Poly.reverse_k (p : Poly) : Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun r => r) (fun hd _ ih r => ih (hd :: r)) p []

theorem Poly.reverse_k_eq (p : Poly) : p.reverse_k = p.reverse := by
  suffices h : ∀ r, List.rec (motive := fun _ => Poly → Poly) (fun r => r) (fun hd _ ih r => ih (hd :: r)) p r
      = List.reverseAux p r by exact h []
  induction p with
  | nil => intro r; rfl
  | cons hd tl ih => intro r; show List.rec (motive := fun _ => Poly → Poly) _ _ tl _ = _; rw [ih]; rfl

/-- One step of `Poly.cancelAux`, with `rec` for the recursive calls. -/
noncomputable def Poly.cancelStep (rec : Poly → Poly → Poly → Poly → Poly × Poly) (m₁ m₂ r₁ r₂ : Poly) : Poly × Poly :=
  List.rec (motive := fun _ => Poly × Poly) (Poly.append_k (Poly.reverse_k r₁) m₁, Poly.reverse_k r₂)
    (fun hd₂ tl₂ _ =>
      List.rec (motive := fun _ => Poly × Poly) (Poly.reverse_k r₁, Poly.append_k (Poly.reverse_k r₂) m₂)
        (fun hd₁ tl₁ _ =>
          Bool.rec
            (Bool.rec
              (Bool.rec
                (Bool.rec (rec tl₁ tl₂ r₁ r₂) (rec tl₁ tl₂ ((Nat.sub hd₁.1 hd₂.1, hd₁.2) :: r₁) r₂) (Nat.blt hd₂.1 hd₁.1))
                (rec tl₁ tl₂ r₁ ((Nat.sub hd₂.1 hd₁.1, hd₁.2) :: r₂)) (Nat.blt hd₁.1 hd₂.1))
              (rec m₁ tl₂ r₁ (hd₂ :: r₂)) (Nat.blt hd₂.2 hd₁.2))
            (rec tl₁ m₂ (hd₁ :: r₁) r₂) (Nat.blt hd₁.2 hd₂.2))
        m₁)
    m₂

noncomputable def Poly.cancelAux_k (fuel : Nat) : Poly → Poly → Poly → Poly → Poly × Poly :=
  Nat.rec (motive := fun _ => Poly → Poly → Poly → Poly → Poly × Poly)
    (fun m₁ m₂ r₁ r₂ => (Poly.append_k (Poly.reverse_k r₁) m₁, Poly.append_k (Poly.reverse_k r₂) m₂))
    (fun _ ih => Poly.cancelStep ih) fuel

theorem Poly.cancelAux_k_eq (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly) :
    Poly.cancelAux_k fuel m₁ m₂ r₁ r₂ = Poly.cancelAux fuel m₁ m₂ r₁ r₂ := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero =>
    show (Poly.append_k (Poly.reverse_k r₁) m₁, Poly.append_k (Poly.reverse_k r₂) m₂) = _
    simp only [cancelAux, append_k_eq, reverse_k_eq]
  | succ fuel ih =>
    have hrec : Poly.cancelAux_k fuel = Poly.cancelAux fuel := by funext a b c d; exact ih a b c d
    show Poly.cancelStep (Poly.cancelAux_k fuel) m₁ m₂ r₁ r₂ = _
    rw [hrec]
    cases m₂ with
    | nil => simp only [cancelStep, cancelAux, append_k_eq, reverse_k_eq]
    | cons hd₂ tl₂ =>
      cases m₁ with
      | nil => simp only [cancelStep, cancelAux, append_k_eq, reverse_k_eq]
      | cons hd₁ tl₁ =>
        cases hd₁; cases hd₂; rename_i k₁ v₁ k₂ v₂
        simp only [cancelStep, cancelAux, cond]
        cases Nat.blt v₁ v₂ <;> cases Nat.blt v₂ v₁ <;> cases Nat.blt k₁ k₂ <;> cases Nat.blt k₂ k₁ <;> rfl

noncomputable def Poly.cancel_k (p₁ p₂ : Poly) : Poly × Poly :=
  Poly.cancelAux_k hugeFuel p₁ p₂ [] []

theorem Poly.cancel_k_eq (p₁ p₂ : Poly) : Poly.cancel_k p₁ p₂ = Poly.cancel p₁ p₂ :=
  Poly.cancelAux_k_eq _ _ _ _ _

noncomputable def Expr.toPoly_k.go (e : Expr) : Nat → Poly → Poly :=
  Expr.rec (motive := fun _ => Nat → Poly → Poly)
    (fun k coeff acc => Bool.rec ((Nat.mul coeff k, fixedVar) :: acc) acc (Nat.beq k 0))
    (fun i coeff acc => (coeff, i) :: acc)
    (fun _ _ iha ihb coeff acc => iha coeff (ihb coeff acc))
    (fun k _ iha coeff acc => Bool.rec (iha (Nat.mul coeff k) acc) acc (Nat.beq k 0))
    (fun _ k iha coeff acc => Bool.rec (iha (Nat.mul coeff k) acc) acc (Nat.beq k 0))
    e

noncomputable def Expr.toPoly_k (e : Expr) : Poly :=
  Expr.toPoly_k.go e 1 []

theorem Expr.toPoly_k_eq (e : Expr) : e.toPoly_k = e.toPoly := by
  suffices h : ∀ coeff acc, Expr.toPoly_k.go e coeff acc = Expr.toPoly.go coeff e acc by exact h 1 []
  induction e with
  | num k =>
    intro coeff acc
    show Bool.rec (motive := fun _ => Poly) _ _ (Nat.beq k 0) = _
    simp only [Expr.toPoly.go, cond]
    cases h : Nat.beq k 0
    · have : (k == 0) = false := h
      simp only [this]; rfl
    · have : (k == 0) = true := h
      simp only [this]; rfl
  | var i => intro coeff acc; rfl
  | add a b iha ihb => intro coeff acc; show Expr.toPoly_k.go a _ (Expr.toPoly_k.go b _ _) = _; rw [ihb, iha]; rfl
  | mulL k a ih =>
    intro coeff acc
    show Bool.rec (motive := fun _ => Poly) (Expr.toPoly_k.go a _ _) _ (Nat.beq k 0) = _
    simp only [Expr.toPoly.go, cond]
    cases h : Nat.beq k 0
    · have : (k == 0) = false := h
      simp only [this]; exact ih _ _
    · have : (k == 0) = true := h
      simp only [this]; rfl
  | mulR a k ih =>
    intro coeff acc
    show Bool.rec (motive := fun _ => Poly) (Expr.toPoly_k.go a _ _) _ (Nat.beq k 0) = _
    simp only [Expr.toPoly.go, cond]
    cases h : Nat.beq k 0
    · have : (k == 0) = false := h
      simp only [this]; exact ih _ _
    · have : (k == 0) = true := h
      simp only [this]; rfl

noncomputable def Expr.toNormPoly_k (e : Expr) : Poly :=
  Poly.norm_k e.toPoly_k

theorem Expr.toNormPoly_k_eq (e : Expr) : e.toNormPoly_k = e.toNormPoly := by
  simp only [toNormPoly_k, Expr.toNormPoly, Expr.toPoly_k_eq, Poly.norm_k_eq]

noncomputable def ExprCnstr.toPoly_k (c : ExprCnstr) : PolyCnstr :=
  { eq := c.eq, lhs := c.lhs.toPoly_k, rhs := c.rhs.toPoly_k }

theorem ExprCnstr.toPoly_k_eq (c : ExprCnstr) : c.toPoly_k = c.toPoly := by
  simp only [toPoly_k, ExprCnstr.toPoly, Expr.toPoly_k_eq]

noncomputable def ExprCnstr.toNormPoly_k (c : ExprCnstr) : PolyCnstr :=
  { eq := c.eq, lhs := (Poly.cancel_k c.lhs.toNormPoly_k c.rhs.toNormPoly_k).1,
    rhs := (Poly.cancel_k c.lhs.toNormPoly_k c.rhs.toNormPoly_k).2 }

theorem ExprCnstr.toNormPoly_k_eq (c : ExprCnstr) : c.toNormPoly_k = c.toNormPoly := by
  simp only [toNormPoly_k, ExprCnstr.toNormPoly, Poly.cancel_k_eq, Expr.toNormPoly_k_eq]

noncomputable def Poly.isZero_k (p : Poly) : Bool :=
  List.rec true (fun _ _ _ => false) p

theorem Poly.isZero_k_eq (p : Poly) : Poly.isZero_k p = p.isZero := by
  cases p <;> rfl

noncomputable def Poly.isNonZero_k (p : Poly) : Bool :=
  List.rec false (fun hd _ ih => Bool.rec ih (Nat.blt 0 hd.1) (Nat.beq hd.2 fixedVar)) p

theorem Poly.isNonZero_k_eq (p : Poly) : Poly.isNonZero_k p = p.isNonZero := by
  induction p with
  | nil => rfl
  | cons hd tl ih =>
    cases hd; rename_i k v
    show Bool.rec (motive := fun _ => Bool) (Poly.isNonZero_k tl) (Nat.blt 0 k) (Nat.beq v fixedVar) = _
    rw [ih]; simp only [Poly.isNonZero, cond]
    cases h : Nat.beq v fixedVar
    · have : (v == fixedVar) = false := h
      simp only [this]
    · have : (v == fixedVar) = true := h
      simp only [this]
      cases h' : Nat.blt 0 k
      · have : ¬ 0 < k := by rw [← Nat.blt_eq, h']; simp
        simp; exact Nat.eq_zero_of_not_pos this
      · have : 0 < k := by rw [← Nat.blt_eq, h']
        simp [this]

noncomputable def PolyCnstr.isUnsat_k (c : PolyCnstr) : Bool :=
  Bool.rec (Poly.isNonZero_k c.lhs && Poly.isZero_k c.rhs)
    ((Poly.isZero_k c.lhs && Poly.isNonZero_k c.rhs) || (Poly.isNonZero_k c.lhs && Poly.isZero_k c.rhs)) c.eq

theorem PolyCnstr.isUnsat_k_eq (c : PolyCnstr) : c.isUnsat_k = c.isUnsat := by
  cases c with
  | mk eq lhs rhs => cases eq <;> simp [isUnsat_k, PolyCnstr.isUnsat, Poly.isZero_k_eq, Poly.isNonZero_k_eq]

noncomputable def PolyCnstr.isValid_k (c : PolyCnstr) : Bool :=
  Bool.rec (Poly.isZero_k c.lhs) (Poly.isZero_k c.lhs && Poly.isZero_k c.rhs) c.eq

theorem PolyCnstr.isValid_k_eq (c : PolyCnstr) : c.isValid_k = c.isValid := by
  cases c with
  | mk eq lhs rhs => cases eq <;> simp [isValid_k, PolyCnstr.isValid, Poly.isZero_k_eq]

noncomputable def Poly.beq'_k (p : Poly) : Poly → Bool :=
  List.rec (motive := fun _ => Poly → Bool) (fun q => List.rec true (fun _ _ _ => false) q)
    (fun hd _ ih q => List.rec false
      (fun hd' tl' _ => Bool.rec false (Bool.rec false (ih tl') (Nat.beq hd.2 hd'.2)) (Nat.beq hd.1 hd'.1)) q) p

theorem Poly.beq'_k_eq (p q : Poly) : Poly.beq'_k p q = true ↔ p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp [Poly.beq'_k]
  | cons hd tl ih =>
    cases hd; rename_i k v
    cases q with
    | nil => simp [Poly.beq'_k]
    | cons hd' tl' =>
      cases hd'; rename_i k' v'
      show Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false (Poly.beq'_k tl tl') (Nat.beq v v')) (Nat.beq k k') = true ↔ _
      cases h₁ : Nat.beq k k'
      · have : k ≠ k' := Nat.ne_of_beq_eq_false h₁
        simp [this]
      · have : k = k' := Nat.eq_of_beq_eq_true h₁
        subst this
        cases h₂ : Nat.beq v v'
        · have : v ≠ v' := Nat.ne_of_beq_eq_false h₂
          simp [this]
        · have : v = v' := Nat.eq_of_beq_eq_true h₂
          subst this; simp [ih]

noncomputable def PolyCnstr.beq'_k (c d : PolyCnstr) : Bool :=
  Bool.rec false (Bool.rec false (Poly.beq'_k c.rhs d.rhs) (Poly.beq'_k c.lhs d.lhs))
    (Bool.rec (Bool.rec true false d.eq) (Bool.rec false true d.eq) c.eq)

theorem PolyCnstr.beq'_k_eq (c d : PolyCnstr) : c.beq'_k d = true → c = d := by
  cases c with
  | mk e₁ l₁ r₁ =>
    cases d with
    | mk e₂ l₂ r₂ =>
      intro h
      cases e₁ <;> cases e₂ <;>
        simp only [beq'_k] at h <;> (try contradiction) <;>
        cases h₁ : Poly.beq'_k l₁ l₂ <;> cases h₂ : Poly.beq'_k r₁ r₂ <;> simp_all [Poly.beq'_k_eq]

theorem ExprCnstr.eq_false_of_isUnsat_k (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly_k.isUnsat_k) :
    c.denote_k ctx = False := by
  rw [ExprCnstr.denote_k_eq_denote]
  exact ExprCnstr.eq_false_of_isUnsat ctx c (by simpa only [ExprCnstr.toNormPoly_k_eq, PolyCnstr.isUnsat_k_eq] using h)

theorem ExprCnstr.eq_true_of_isValid_k (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly_k.isValid_k) :
    c.denote_k ctx = True := by
  rw [ExprCnstr.denote_k_eq_denote]
  exact ExprCnstr.eq_true_of_isValid ctx c (by simpa only [ExprCnstr.toNormPoly_k_eq, PolyCnstr.isValid_k_eq] using h)

theorem ExprCnstr.eq_of_toNormPoly_eq_k (ctx : Context) (c d : ExprCnstr) (h : c.toNormPoly_k.beq'_k d.toPoly_k) :
    c.denote_k ctx = d.denote_k ctx := by
  rw [ExprCnstr.denote_k_eq_denote, ExprCnstr.denote_k_eq_denote]
  have h := PolyCnstr.beq'_k_eq _ _ h
  rw [ExprCnstr.toNormPoly_k_eq, ExprCnstr.toPoly_k_eq] at h
  exact ExprCnstr.eq_of_toNormPoly_eq ctx c d (by simp [h])

theorem Expr.eq_of_toNormPoly_eq_k (ctx : Context) (e e' : Expr) (h : Poly.beq'_k e.toNormPoly_k e'.toPoly_k) :
    e.denote_k ctx = e'.denote_k ctx := by
  rw [Expr.denote_k_eq_denote, Expr.denote_k_eq_denote]
  have h := (Poly.beq'_k_eq _ _).mp h
  rw [Expr.toNormPoly_k_eq, Expr.toPoly_k_eq] at h
  exact Expr.eq_of_toNormPoly_eq ctx e e' (by simp [h])

end Internal.Linear

def Internal.elimOffset {α : Sort u} (a b k : Nat) (h₁ : a + k = b + k) (h₂ : a = b → α) : α :=
  h₂ (Nat.add_right_cancel h₁)

end Nat
