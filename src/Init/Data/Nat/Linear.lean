/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.ByCases
import Init.Data.Prod
import Init.Data.RArray

namespace Nat.Linear

/-!
  Helper definitions and theorems for constructing linear arithmetic proofs.
-/

abbrev Var := Nat

abbrev Context := Lean.RArray Nat

/--
  When encoding polynomials. We use `fixedVar` for encoding numerals.
  The denotation of `fixedVar` is always `1`. -/
def fixedVar := 100000000 -- Any big number should work here

def Var.denote (ctx : Context) (v : Var) : Nat :=
  bif v == fixedVar then 1 else ctx.get v

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited

def Expr.denote (ctx : Context) : Expr → Nat
  | .add a b  => Nat.add (denote ctx a) (denote ctx b)
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => Nat.mul k (denote ctx e)
  | .mulR e k => Nat.mul (denote ctx e) k

abbrev Poly := List (Nat × Var)

def Poly.denote (ctx : Context) (p : Poly) : Nat :=
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

def Poly.denote_eq (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx = mp.2.denote ctx

def Poly.denote_le (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx ≤ mp.2.denote ctx

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
  deriving BEq

-- TODO: implement LawfulBEq generator companion for BEq
instance : LawfulBEq PolyCnstr where
  eq_of_beq {a b} h := by
    cases a; rename_i eq₁ lhs₁ rhs₁
    cases b; rename_i eq₂ lhs₂ rhs₂
    have h : eq₁ == eq₂ && (lhs₁ == lhs₂ && rhs₁ == rhs₂) := h
    simp at h
    have ⟨h₁, h₂, h₃⟩ := h
    rw [h₁, h₂, h₃]
  rfl {a} := by
    cases a; rename_i eq lhs rhs
    show (eq == eq && (lhs == lhs && rhs == rhs)) = true
    simp [LawfulBEq.rfl]

structure ExprCnstr where
  eq  : Bool
  lhs : Expr
  rhs : Expr

def PolyCnstr.denote (ctx : Context) (c : PolyCnstr) : Prop :=
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

def ExprCnstr.denote (ctx : Context) (c : ExprCnstr) : Prop :=
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
      · simp only [insert, h₁, h₂, cond_false, cond_true]
        simp [Nat.eq_of_beq_eq_true h₂]
      · simp only [insert, h₁, h₂, cond_false, cond_true]
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
  | _ :: m => simp [denote_cons]

attribute [local simp] Poly.denote_cons

theorem Poly.denote_reverseAux (ctx : Context) (p q : Poly) : denote ctx (List.reverseAux p q) = denote ctx (p ++ q) := by
  match p with
  | [] => simp [List.reverseAux]
  | (k, v) :: p => simp [List.reverseAux, denote_reverseAux]

attribute [local simp] Poly.denote_reverseAux

theorem Poly.denote_reverse (ctx : Context) (p : Poly) : denote ctx (List.reverse p) = denote ctx p := by
  simp [List.reverse]

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
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [hltv]
    · apply ih; simp [denote_eq] at h |-; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [hgtv]
      · apply ih; simp [denote_eq] at h |-; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [hltk]
        · apply ih
          simp [denote_eq] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Eq.symm
          apply Nat.sub_eq_of_eq_add
          simp [h]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [hgtk]
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
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [hltv] at h
    · have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [hgtv] at h
      · have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [hltk] at h
        · have ih := ih (h := h); simp [denote_eq] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih.symm
          simp at ih
          rw [ih]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [hgtk] at h
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
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [hltv]
    · apply ih; simp [denote_le] at h |-; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [hgtv]
      · apply ih; simp [denote_le] at h |-; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [hltk]
        · apply ih
          simp [denote_le] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Nat.le_sub_of_add_le
          simp [h]
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [hgtk]
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
    by_cases hltv : Nat.blt v₁ v₂ <;> simp [hltv] at h
    · have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
    · by_cases hgtv : Nat.blt v₂ v₁ <;> simp [hgtv] at h
      · have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
      · have heqv : v₁ = v₂ := eq_of_not_blt_eq_true hltv hgtv; subst heqv
        by_cases hltk : Nat.blt k₁ k₂ <;> simp [hltk] at h
        · have ih := ih (h := h); simp [denote_le] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt (Nat.blt_eq.mp hltk))
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have := Nat.add_le_of_le_sub (Nat.le_trans haux (Nat.le_add_left ..)) ih
          simp at this
          exact this
        · by_cases hgtk : Nat.blt k₂ k₁ <;> simp [hgtk] at h
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
  | case5 k k' a h => simp [toPoly.go, h, eq_of_beq h]
  | case6 k a k' h ih =>
    simp only [toPoly.go, denote, mul_eq]
    simp [h, cond_false, ih, Nat.mul_assoc]
  | case7 k a k' h =>
    simp only [toPoly.go, denote, mul_eq]
    simp [h, eq_of_beq h]
  | case8 k a k' h ih =>
    simp only [toPoly.go, denote, mul_eq]
    simp [h, cond_false, ih, Nat.mul_assoc]

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

theorem ExprCnstr.toPoly_norm_eq (c : ExprCnstr) : c.toPoly.norm = c.toNormPoly :=
  rfl

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
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le, -and_imp]
  · intro
      | Or.inl ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₁]; have := Nat.ne_zero_of_lt (Poly.of_isNonZero ctx h₂); simp [this.symm]
      | Or.inr ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₂]; have := Nat.ne_zero_of_lt (Poly.of_isNonZero ctx h₁); simp [this]
  · intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₂]
    exact Poly.of_isNonZero ctx h₁

theorem PolyCnstr.eq_true_of_isValid (ctx : Context) {c : PolyCnstr} : c.isValid → c.denote ctx = True := by
  cases c; rename_i eq lhs rhs
  simp [isValid]
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le, -and_imp]
  · intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₁, h₂]
  · intro h
    simp [Poly.of_isZero, h]

theorem ExprCnstr.eq_false_of_isUnsat (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isUnsat) : c.denote ctx = False := by
  have := PolyCnstr.eq_false_of_isUnsat ctx h
  simp [-eq_iff_iff] at this
  assumption

theorem ExprCnstr.eq_true_of_isValid (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isValid) : c.denote ctx = True := by
  have := PolyCnstr.eq_true_of_isValid ctx h
  simp [-eq_iff_iff] at this
  assumption

theorem ExprCnstr.eq_of_toNormPoly_eq (ctx : Context) (c d : ExprCnstr) (h : c.toNormPoly == d.toPoly) : c.denote ctx = d.denote ctx := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  simp [-eq_iff_iff] at h
  assumption

theorem Expr.eq_of_toNormPoly_eq (ctx : Context) (e e' : Expr) (h : e.toNormPoly == e'.toPoly) : e.denote ctx = e'.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Expr.toNormPoly, Poly.norm] at h
  assumption

end Linear

def elimOffset {α : Sort u} (a b k : Nat) (h₁ : a + k = b + k) (h₂ : a = b → α) : α :=
  h₂ (Nat.add_right_cancel h₁)

end Nat
