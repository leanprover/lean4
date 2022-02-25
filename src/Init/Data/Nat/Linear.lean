/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Coe
import Init.Classical
import Init.SimpLemmas
import Init.Data.Nat.Basic
import Init.Data.List.Basic
import Init.Data.Prod

namespace Nat.Linear

/--!
  Helper definitions and theorems for constructing linear arithmetic proofs.
-/

abbrev Var := Nat

abbrev Context := List Nat

/--
  When encoding polynomials. We use `fixedVar` for encoding numerals.
  The denotation of `fixedVar` is always `1`. -/
def fixedVar := 100000000 -- Any big number should work here

def Var.denote (ctx : Context) (v : Var) : Nat :=
  if v = fixedVar then 1 else go ctx v
where
  go : List Nat → Nat → Nat
   | [],    i   => 0
   | a::as, 0   => a
   | _::as, i+1 => go as i

inductive Expr where
  | num  (v : Nat)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Nat) (a : Expr)
  | mulR (a : Expr) (k : Nat)
  deriving Inhabited

def Expr.denote (ctx : Context) : Expr → Nat
  | Expr.add a b  => Nat.add (denote ctx a) (denote ctx b)
  | Expr.num k    => k
  | Expr.var v    => v.denote ctx
  | Expr.mulL k e => k * denote ctx e
  | Expr.mulR e k => denote ctx e * k

abbrev Poly := List (Nat × Var)

def Poly.denote (ctx : Context) (p : Poly) : Nat :=
  match p with
  | [] => 0
  | (k, v) :: p => k * v.denote ctx + denote ctx p

def Poly.insertSorted (k : Nat) (v : Var) (p : Poly) : Poly :=
  match p with
  | [] => [(k, v)]
  | (k', v') :: p => if v < v' then (k, v) :: (k', v') :: p else (k', v') :: insertSorted k v p

def Poly.sort (p : Poly) : Poly :=
  let rec go (p : Poly) (r : Poly) : Poly :=
    match p with
    | [] => r
    | (k, v) :: p => go p (r.insertSorted k v)
  go p []

def Poly.fuse (p : Poly) : Poly :=
  match p with
  | []  => []
  | (k, v) :: p =>
    match fuse p with
    | [] => [(k, v)]
    | (k', v') :: p' => if v = v' then (k+k', v)::p' else (k, v) :: (k', v') :: p'

def Poly.mul (k : Nat) (p : Poly) : Poly :=
  if k = 0 then
    []
  else if k = 1 then
    p
  else
    go p
where
  go : Poly → Poly
  | [] => []
  | (k', v) :: p => (k*k', v) :: go p

def Poly.cancelAux (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly) : Poly × Poly :=
  match fuel with
  | 0 => (r₁.reverse ++ m₁, r₂.reverse ++ m₂)
  | fuel + 1 =>
    match m₁, m₂ with
    | m₁, [] => (r₁.reverse ++ m₁, r₂.reverse)
    | [], m₂ => (r₁.reverse, r₂.reverse ++ m₂)
    | (k₁, v₁) :: m₁, (k₂, v₂) :: m₂ =>
      if v₁ < v₂ then
        cancelAux fuel m₁ ((k₂, v₂) :: m₂) ((k₁, v₁) :: r₁) r₂
      else if v₁ > v₂ then
        cancelAux fuel ((k₁, v₁) :: m₁) m₂ r₁ ((k₂, v₂) :: r₂)
      else if k₁ < k₂ then
        cancelAux fuel m₁ m₂ r₁ ((k₂ - k₁, v₁) :: r₂)
      else if k₁ > k₂ then
        cancelAux fuel m₁ m₂ ((k₁ - k₂, v₁) :: r₁) r₂
      else
        cancelAux fuel m₁ m₂ r₁ r₂

def Poly.cancel (p₁ p₂ : Poly) : Poly × Poly :=
  cancelAux (p₁.length + p₂.length) p₁ p₂ [] []

def Poly.isNum? (p : Poly) : Option Nat :=
  match p with
  | [] => some 0
  | [(k, v)] => if v = fixedVar then some k else none
  | _ => none

def Poly.isZero (p : Poly) : Bool :=
  match p with
  | [] => true
  | _  => false

def Poly.isNonZero (p : Poly) : Bool :=
  match p with
  | [] => false
  | (k, v) :: p => if v = fixedVar then k > 0 else isNonZero p

def Poly.denote_eq (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx = mp.2.denote ctx

def Poly.denote_le (ctx : Context) (mp : Poly × Poly) : Prop := mp.1.denote ctx ≤ mp.2.denote ctx

def Expr.toPoly : Expr → Poly
  | Expr.num k    => if k = 0 then [] else [ (k, fixedVar) ]
  | Expr.var i    => [(1, i)]
  | Expr.add a b  => a.toPoly ++ b.toPoly
  | Expr.mulL k a => a.toPoly.mul k
  | Expr.mulR a k => a.toPoly.mul k

def Expr.toNormPoly (e : Expr) : Poly :=
  e.toPoly.sort.fuse

def Expr.inc (e : Expr) : Expr :=
   Expr.add e (Expr.num 1)

structure PolyCnstr  where
  eq  : Bool
  lhs : Poly
  rhs : Poly
  deriving BEq

-- TODO: implement LawfulBEq generator companion for BEq
instance : LawfulBEq PolyCnstr where
  eq_of_beq a b h := by
    cases a; rename_i eq₁ lhs₁ rhs₁
    cases b; rename_i eq₂ lhs₂ rhs₂
    have h : eq₁ == eq₂ && lhs₁ == lhs₂ && rhs₁ == rhs₂ := h
    simp at h
    have ⟨⟨h₁, h₂⟩, h₃⟩ := h
    rw [h₁, eq_of_beq h₂, eq_of_beq h₃]

def PolyCnstr.mul (k : Nat) (c : PolyCnstr) : PolyCnstr :=
  { c with lhs := c.lhs.mul k, rhs := c.rhs.mul k }

def PolyCnstr.combine (c₁ c₂ : PolyCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel (c₁.lhs ++ c₂.lhs).sort.fuse (c₁.rhs ++ c₂.rhs).sort.fuse
  { eq := c₁.eq && c₂.eq, lhs, rhs }

structure ExprCnstr where
  eq  : Bool
  lhs : Expr
  rhs : Expr

def PolyCnstr.denote (ctx : Context) (c : PolyCnstr) : Prop :=
  if c.eq then
    Poly.denote_eq ctx (c.lhs, c.rhs)
  else
    Poly.denote_le ctx (c.lhs, c.rhs)

def PolyCnstr.norm (c : PolyCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.sort.fuse c.rhs.sort.fuse
  { eq := c.eq, lhs, rhs }

def PolyCnstr.isUnsat (c : PolyCnstr) : Bool :=
  if c.eq then
    (c.lhs.isZero && c.rhs.isNonZero) || (c.lhs.isNonZero && c.rhs.isZero)
  else
    c.lhs.isNonZero && c.rhs.isZero

def PolyCnstr.isValid (c : PolyCnstr) : Bool :=
  if c.eq then
    c.lhs.isZero && c.rhs.isZero
  else
    c.lhs.isZero

/-- Return true iff `c₁` has fewer monomials than `c₂`. -/
def PolyCnstr.hasFewerMonomials (c₁ c₂ : PolyCnstr) : Bool :=
  c₁.lhs.length + c₁.rhs.length < c₂.lhs.length + c₂.rhs.length

def ExprCnstr.denote (ctx : Context) (c : ExprCnstr) : Prop :=
  if c.eq then
    c.lhs.denote ctx = c.rhs.denote ctx
  else
    c.lhs.denote ctx ≤ c.rhs.denote ctx

def ExprCnstr.toPoly (c : ExprCnstr) : PolyCnstr :=
  { c with lhs := c.lhs.toPoly, rhs := c.rhs.toPoly }

def ExprCnstr.toNormPoly (c : ExprCnstr) : PolyCnstr :=
  let (lhs, rhs) := Poly.cancel c.lhs.toNormPoly c.rhs.toNormPoly
  { c with lhs, rhs }

abbrev Certificate := List (Nat × ExprCnstr)

def Certificate.combineHyps (c : PolyCnstr) (hs : Certificate) : PolyCnstr :=
  match hs with
  | [] => c
  | (k, c') :: hs => combineHyps (PolyCnstr.combine c (c'.toNormPoly.mul (k+1))) hs

def Certificate.combine (hs : Certificate) : PolyCnstr :=
  match hs with
  | [] => { eq := true, lhs := [], rhs := [] }
  | (k, c) :: hs => combineHyps (c.toNormPoly.mul (k+1)) hs

def Certificate.denote (ctx : Context) (c : Certificate) : Prop :=
  match c with
  | [] => False
  | (_, c)::hs => c.denote ctx → denote ctx hs

def monomialToExpr (k : Nat) (v : Var) : Expr :=
  if v = fixedVar then
    Expr.num k
  else if k = 1 then
    Expr.var v
  else
    Expr.mulL k (Expr.var v)

def Poly.toExpr (p : Poly) : Expr :=
  match p with
  | [] => Expr.num 0
  | (k, v) :: p => go (monomialToExpr k v) p
where
  go (e : Expr) (p : Poly) : Expr :=
    match p with
    | [] => e
    | (k, v) :: p => go (Expr.add e (monomialToExpr k v)) p

attribute [local simp] Nat.add_comm Nat.add_assoc Nat.add_left_comm Nat.right_distrib Nat.left_distrib Nat.mul_assoc Nat.mul_comm
attribute [local simp] Poly.denote Expr.denote Poly.insertSorted Poly.sort Poly.sort.go Poly.fuse Poly.cancelAux
attribute [local simp] Poly.mul Poly.mul.go

theorem Poly.denote_insertSorted (ctx : Context) (k : Nat) (v : Var) (p : Poly) : (p.insertSorted k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  match p with
  | [] => simp
  | (k', v') :: p => by_cases h : v < v' <;> simp [h, denote_insertSorted]

attribute [local simp] Poly.denote_insertSorted

theorem Poly.denote_sort_go (ctx : Context) (p : Poly) (r : Poly) : (sort.go p r).denote ctx = p.denote ctx + r.denote ctx := by
  match p with
  | [] => simp
  | (k, v):: p => simp [denote_sort_go]

attribute [local simp] Poly.denote_sort_go

theorem Poly.denote_sort (ctx : Context) (m : Poly) : m.sort.denote ctx = m.denote ctx := by
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

theorem Poly.denote_fuse (ctx : Context) (p : Poly) : p.fuse.denote ctx = p.denote ctx := by
  match p with
  | [] => rfl
  | (k, v) :: p =>
    have ih := denote_fuse ctx p
    simp
    split
    case _ h => simp [← ih, h]
    case _ k' v' p' h => by_cases he : v = v' <;> simp [he, ← ih, h]

attribute [local simp] Poly.denote_fuse

theorem Poly.denote_mul (ctx : Context) (k : Nat) (p : Poly) : (p.mul k).denote ctx = k * p.denote ctx := by
  simp
  by_cases h : k = 0 <;> simp [h]
  by_cases h : k = 1 <;> simp [h]
  induction p with
  | nil  => simp
  | cons kv m ih => cases kv with | _ k' v => simp [ih]

attribute [local simp] Poly.denote_mul

theorem Poly.denote_eq_cancelAux (ctx : Context) (fuel : Nat) (m₁ m₂ r₁ r₂ : Poly)
    (h : denote_eq ctx (r₁.reverse ++ m₁, r₂.reverse ++ m₂)) : denote_eq ctx (cancelAux fuel m₁ m₂ r₁ r₂) := by
  induction fuel generalizing m₁ m₂ r₁ r₂ with
  | zero => assumption
  | succ fuel ih =>
    simp
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_eq] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_eq] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_eq] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Eq.symm
          apply Nat.sub_eq_of_eq_add
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_eq] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_eq_of_eq_add
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
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
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_eq] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_eq] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih.symm
          simp at ih
          rw [ih]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_eq] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have ih := Nat.eq_add_of_sub_eq (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at ih
            rw [ih]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_eq] at ih ⊢
            rw [← Nat.add_assoc, ih, Nat.add_assoc]

theorem Poly.denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (m₁, m₂)) : denote_eq ctx (cancel m₁ m₂) := by
  simp; apply denote_eq_cancelAux; simp [h]

theorem Poly.of_denote_eq_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_eq ctx (cancel m₁ m₂)) : denote_eq ctx (m₁, m₂) := by
  simp at h
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
    split <;> simp at h <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv]
    . apply ih; simp [denote_le] at h |-; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv]
      . apply ih; simp [denote_le] at h |-; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk]
        . apply ih
          simp [denote_le] at h |-
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
          apply Nat.le_sub_of_add_le
          simp [h]
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk]
          . apply ih
            simp [denote_le] at h |-
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux]
            apply Nat.sub_le_of_le_add (Nat.le_trans haux (Nat.le_add_left ..))
            simp [h]
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
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
    split at h <;> simp <;> try assumption
    rename_i k₁ v₁ m₁ k₂ v₂ m₂
    by_cases hltv : v₁ < v₂ <;> simp [hltv] at h
    . have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
    . by_cases hgtv : v₁ > v₂ <;> simp [hgtv] at h
      . have ih := ih (h := h); simp [denote_le] at ih ⊢; assumption
      . have heqv : v₁ = v₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtv) (Nat.ge_of_not_lt hltv); subst heqv
        by_cases hltk : k₁ < k₂ <;> simp [hltk] at h
        . have ih := ih (h := h); simp [denote_le] at ih ⊢
          have haux : k₁ * Var.denote ctx v₁ ≤ k₂ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hltk)
          rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
          have := Nat.add_le_of_le_sub (Nat.le_trans haux (Nat.le_add_left ..)) ih
          simp at this
          exact this
        . by_cases hgtk : k₁ > k₂ <;> simp [hgtk] at h
          . have ih := ih (h := h); simp [denote_le] at ih ⊢
            have haux : k₂ * Var.denote ctx v₁ ≤ k₁ * Var.denote ctx v₁ := Nat.mul_le_mul_right _ (Nat.le_of_lt hgtk)
            rw [Nat.mul_sub_right_distrib, ← Nat.add_assoc, ← Nat.add_sub_assoc haux] at ih
            have := Nat.le_add_of_sub_le (Nat.le_trans haux (Nat.le_add_left ..)) ih
            simp at this
            exact this
          . have heqk : k₁ = k₂ := Nat.le_antisymm (Nat.ge_of_not_lt hgtk) (Nat.ge_of_not_lt hltk); subst heqk
            have ih := ih (h := h); simp [denote_le] at ih ⊢
            have := Nat.add_le_add_right ih (k₁ * Var.denote ctx v₁)
            simp at this
            exact this

theorem Poly.denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (m₁, m₂)) : denote_le ctx (cancel m₁ m₂) := by
  simp; apply denote_le_cancelAux; simp [h]

theorem Poly.of_denote_le_cancel {ctx : Context} {m₁ m₂ : Poly} (h : denote_le ctx (cancel m₁ m₂)) : denote_le ctx (m₁, m₂) := by
  simp at h
  have := Poly.of_denote_le_cancelAux (h := h)
  simp at this
  assumption

theorem Poly.denote_le_cancel_eq (ctx : Context) (m₁ m₂ : Poly) : denote_le ctx (cancel m₁ m₂) = denote_le ctx (m₁, m₂) :=
  propext <| Iff.intro (fun h => of_denote_le_cancel h) (fun h => denote_le_cancel h)

attribute [local simp] Poly.denote_le_cancel_eq

@[simp] theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  induction e with
  | num k => by_cases h : k = 0 <;> simp [toPoly, h, Var.denote]
  | var i => simp [toPoly]
  | add a b iha ihb => simp [toPoly, iha, ihb]
  | mulL k a ih => simp [toPoly, ih, -Poly.mul]
  | mulR k a ih => simp [toPoly, ih, -Poly.mul]

theorem Expr.eq_of_toNormPoly (ctx : Context) (a b : Expr) (h : a.toNormPoly = b.toNormPoly) : a.denote ctx = b.denote ctx := by
  simp [toNormPoly] at h
  have h := congrArg (Poly.denote ctx) h
  simp at h
  assumption

theorem Expr.of_cancel_eq (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx = b.denote ctx) = (c.denote ctx = d.denote ctx) := by
  have := Poly.denote_eq_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.denote_eq] at this
  exact this.symm

theorem Expr.of_cancel_le (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.toNormPoly b.toNormPoly = (c.toPoly, d.toPoly)) : (a.denote ctx ≤ b.denote ctx) = (c.denote ctx ≤ d.denote ctx) := by
  have := Poly.denote_le_cancel_eq ctx a.toNormPoly b.toNormPoly
  rw [h] at this
  simp [toNormPoly, Poly.denote_le] at this
  exact this.symm

theorem Expr.of_cancel_lt (ctx : Context) (a b c d : Expr) (h : Poly.cancel a.inc.toNormPoly b.toNormPoly = (c.inc.toPoly, d.toPoly)) : (a.denote ctx < b.denote ctx) = (c.denote ctx < d.denote ctx) :=
  of_cancel_le ctx a.inc b c.inc d h

theorem ExprCnstr.toPoly_norm_eq (c : ExprCnstr) : c.toPoly.norm = c.toNormPoly :=
  rfl

theorem ExprCnstr.denote_toNormPoly (ctx : Context) (c : ExprCnstr) : c.toNormPoly.denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  simp [ExprCnstr.denote, PolyCnstr.denote, ExprCnstr.toNormPoly]
  by_cases h : eq = true <;> simp [h]
  . rw [Poly.denote_eq_cancel_eq]; simp [Poly.denote_eq, Expr.toNormPoly]
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_le, Expr.toNormPoly]

attribute [local simp] ExprCnstr.denote_toNormPoly

theorem Poly.mul.go_denote (ctx : Context) (k : Nat) (p : Poly) : (Poly.mul.go k p).denote ctx = k * p.denote ctx := by
  match p with
  | [] => rfl
  | (k', v) :: p => simp [Poly.mul.go, go_denote]

attribute [local simp] Poly.mul.go_denote

section
attribute [-simp] Nat.right_distrib Nat.left_distrib

theorem PolyCnstr.denote_mul (ctx : Context) (k : Nat) (c : PolyCnstr) : (c.mul (k+1)).denote ctx = c.denote ctx := by
  cases c; rename_i eq lhs rhs
  have hn : ¬ (k + 1 = 0) := Nat.succ_ne_zero k
  by_cases he : eq = true <;> simp [he, PolyCnstr.mul, PolyCnstr.denote, Poly.denote_le, Poly.denote_eq]
    <;> by_cases hk : k = 0 <;> simp [hk, hn] <;> apply propext <;> apply Iff.intro <;> intro h
  . exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ _) h
  . rw [h]
  . exact Nat.le_of_mul_le_mul_left h (Nat.zero_lt_succ _)
  . apply Nat.mul_le_mul_left _ h

end

attribute [local simp] PolyCnstr.denote_mul

theorem PolyCnstr.denote_combine {ctx : Context} {c₁ c₂ : PolyCnstr} (h₁ : c₁.denote ctx) (h₂ : c₂.denote ctx) : (c₁.combine c₂).denote ctx := by
  cases c₁; cases c₂; rename_i eq₁ lhs₁ rhs₁ eq₂ lhs₂ rhs₂
  simp [denote] at h₁ h₂
  simp [PolyCnstr.combine, denote]
  by_cases he₁ : eq₁ = true <;> by_cases he₂ : eq₂ = true <;> simp [he₁, he₂] at h₁ h₂ |-
  . rw [Poly.denote_eq_cancel_eq]; simp [Poly.denote_eq] at h₁ h₂ |-; simp [h₁, h₂]
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; rw [h₁]; apply Nat.add_le_add_left h₂
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; rw [h₂]; apply Nat.add_le_add_right h₁
  . rw [Poly.denote_le_cancel_eq]; simp [Poly.denote_eq, Poly.denote_le] at h₁ h₂ |-; apply Nat.add_le_add h₁ h₂

attribute [local simp] PolyCnstr.denote_combine

theorem Poly.isNum?_eq_some (ctx : Context) {p : Poly} {k : Nat} : p.isNum? = some k → p.denote ctx = k := by
  simp [isNum?]
  split
  next => intro h; injection h; subst k; simp
  next k v => by_cases h : v = fixedVar <;> simp [h]; intros; simp [Var.denote]; assumption
  next => intros; contradiction

def Poly.of_isZero (ctx : Context) {p : Poly} (h : isZero p = true) : p.denote ctx = 0 := by
  simp [isZero] at h
  split at h
  . simp
  . contradiction

def Poly.of_isNonZero (ctx : Context) {p : Poly} (h : isNonZero p = true) : p.denote ctx > 0 := by
  match p with
  | [] => contradiction
  | (k, v) :: p =>
    by_cases he : v = fixedVar <;> simp [he, isNonZero] at h ⊢
    . simp [Var.denote]; apply Nat.lt_of_succ_le; exact Nat.le_trans h (Nat.le_add_right ..)
    . have ih := of_isNonZero ctx h
      exact Nat.le_trans ih (Nat.le_add_right ..)

def PolyCnstr.eq_false_of_isUnsat (ctx : Context) {c : PolyCnstr} : c.isUnsat → c.denote ctx = False := by
  cases c; rename_i eq lhs rhs
  simp [isUnsat]
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le]
  . intro
      | Or.inl ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₁]; have := Nat.not_eq_zero_of_lt (Poly.of_isNonZero ctx h₂); simp [this.symm]
      | Or.inr ⟨h₁, h₂⟩ => simp [Poly.of_isZero, h₂]; have := Nat.not_eq_zero_of_lt (Poly.of_isNonZero ctx h₁); simp [this]
  . intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₂]
    have := Nat.not_le_of_gt (Poly.of_isNonZero ctx h₁)
    simp [this]

def PolyCnstr.eq_true_of_isValid (ctx : Context) {c : PolyCnstr} : c.isValid → c.denote ctx = True := by
  cases c; rename_i eq lhs rhs
  simp [isValid]
  by_cases he : eq = true <;> simp [he, denote, Poly.denote_eq, Poly.denote_le]
  . intro ⟨h₁, h₂⟩
    simp [Poly.of_isZero, h₁, h₂]
  . intro h
    simp [Poly.of_isZero, h]
    have := Nat.zero_le (Poly.denote ctx rhs)
    simp [this]

def ExprCnstr.eq_false_of_isUnsat (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isUnsat) : c.denote ctx = False := by
  have := PolyCnstr.eq_false_of_isUnsat ctx h
  simp at this
  assumption

def ExprCnstr.eq_true_of_isValid (ctx : Context) (c : ExprCnstr) (h : c.toNormPoly.isValid) : c.denote ctx = True := by
  have := PolyCnstr.eq_true_of_isValid ctx h
  simp at this
  assumption

theorem Certificate.of_combineHyps (ctx : Context) (c : PolyCnstr) (cs : Certificate) (h : (combineHyps c cs).denote ctx → False) : c.denote ctx → cs.denote ctx := by
  match cs with
  | [] => simp [combineHyps, denote] at *; exact h
  | (k, c')::cs =>
    intro h₁ h₂
    have := PolyCnstr.denote_combine (ctx := ctx) (c₂ := PolyCnstr.mul (k + 1) (ExprCnstr.toNormPoly c')) h₁
    simp at this
    have := this h₂
    have ih := of_combineHyps ctx (PolyCnstr.combine c (PolyCnstr.mul (k + 1) (ExprCnstr.toNormPoly c'))) cs
    exact ih h this

theorem Certificate.of_combine (ctx : Context) (cs : Certificate) (h : cs.combine.denote ctx → False) : cs.denote ctx := by
  match cs with
  | [] => simp [combine, PolyCnstr.denote, Poly.denote_eq] at h
  | (k, c)::cs =>
    simp [denote, combine] at *
    intro h'
    apply of_combineHyps (h := h)
    simp [h']

theorem Certificate.of_combine_isUnsat (ctx : Context) (cs : Certificate) (h : cs.combine.isUnsat) : cs.denote ctx :=
  have h := PolyCnstr.eq_false_of_isUnsat ctx h
  of_combine ctx cs (fun h' => Eq.mp h h')

theorem denote_monomialToExpr (ctx : Context) (k : Nat) (v : Var) : (monomialToExpr k v).denote ctx = k * v.denote ctx := by
  simp [monomialToExpr]
  by_cases h : v = fixedVar <;> simp [h, Expr.denote]
  . simp [Var.denote]
  . by_cases h : k = 1 <;> simp [h, Expr.denote]

attribute [local simp] denote_monomialToExpr

theorem Poly.denote_toExpr_go (ctx : Context) (e : Expr) (p : Poly) : (toExpr.go e p).denote ctx = e.denote ctx + p.denote ctx := by
  induction p generalizing e with
  | nil => simp [toExpr.go, Poly.denote]
  | cons kv p ih => cases kv; simp [toExpr.go, ih, Expr.denote, Poly.denote]

attribute [local simp] Poly.denote_toExpr_go

theorem Poly.denote_toExpr (ctx : Context) (p : Poly) : p.toExpr.denote ctx = p.denote ctx := by
  match p with
  | [] => simp [toExpr, Expr.denote, Poly.denote]
  | (k, v) :: p => simp [toExpr, Expr.denote, Poly.denote]

theorem ExprCnstr.eq_of_toNormPoly_eq (ctx : Context) (e : ExprCnstr) (p : PolyCnstr) (h : e.toNormPoly == p) : e.denote ctx = p.denote ctx := by
  simp [← eq_of_beq h]

end Nat.Linear
