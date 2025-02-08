
/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.ByCases
import Init.Data.Prod
import Init.Data.Int.Lemmas
import Init.Data.Int.LemmasAux
import Init.Data.RArray

namespace Int.Linear

/-! Helper definitions and theorems for constructing linear arithmetic proofs. -/

abbrev Var := Nat
abbrev Context := Lean.RArray Int

/--
When encoding polynomials. We use `fixedVar` for encoding numerals.
The denotation of `fixedVar` is always `1`. -/
def fixedVar := 100000000 -- Any big number should work here

def Var.denote (ctx : Context) (v : Var) : Int :=
  bif v == fixedVar then 1 else ctx.get v

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | add  (a b : Expr)
  | mulL (k : Int) (a : Expr)
  | mulR (a : Expr) (k : Int)
  deriving Inhabited

def Expr.denote (ctx : Context) : Expr → Int
  | .add a b  => Int.add (denote ctx a) (denote ctx b)
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => Int.mul k (denote ctx e)
  | .mulR e k => Int.mul (denote ctx e) k

inductive Poly where
  | zero
  | add (k : Int) (v : Var) (p : Poly)
  deriving BEq

def Poly.denote (ctx : Context) (p : Poly) : Int :=
  match p with
  | .zero => 0
  | .add k v p => Int.add (Int.mul k (v.denote ctx)) (denote ctx p)

def Poly.insert (k : Int) (v : Var) (p : Poly) : Poly :=
  match p with
  | .zero => .add k v .zero
  | .add k' v' p =>
    bif Nat.blt v v' then
      .add k v <| .add k' v' p
    else bif Nat.beq v v' then
      .add (Int.add k k') v' p
    else
      .add k' v' (insert k v p)

def Poly.norm (p : Poly) : Poly := go p .zero
where
  go (p : Poly) (r : Poly) : Poly :=
    match p with
    | .zero => r
    | .add k v p => go p (r.insert k v)

def Poly.sub (p₁ : Poly) (p₂ : Poly) : Poly :=
  match p₂ with
  | .zero =>  p₁
  | .add k v p₂ => sub (p₁.insert (-k) v) p₂

def Expr.toPoly (e : Expr) :=
  go 1 e .zero
where
  -- Implementation note: This assembles the result using difference lists
  -- to avoid `++` on lists.
  go (coeff : Int) : Expr → (Poly → Poly)
    | .num k    => bif k == 0 then id else (.add (Int.mul coeff k) fixedVar ·)
    | .var v    => (.add coeff v ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .mulL k a
    | .mulR a k => bif k == 0 then id else go (Int.mul coeff k) a

def Expr.toNormPoly (e : Expr) : Poly :=
  e.toPoly.norm

inductive PolyCnstr  where
  | eq (p : Poly)
  | le (p : Poly)
  deriving BEq

def PolyCnstr.denote (ctx : Context) : PolyCnstr → Prop
  | .eq p => p.denote ctx = 0
  | .le p => p.denote ctx ≤ 0

def PolyCnstr.norm : PolyCnstr → PolyCnstr
  | .eq p => .eq p.norm
  | .le p => .le p.norm

inductive ExprCnstr  where
  | eq (p₁ p₂ : Expr)
  | le (p₁ p₂ : Expr)
  deriving Inhabited

def ExprCnstr.denote (ctx : Context) : ExprCnstr → Prop
  | .eq p₁ p₂ => p₁.denote ctx = p₂.denote ctx
  | .le p₁ p₂ => p₁.denote ctx ≤ p₂.denote ctx

def ExprCnstr.toPoly : ExprCnstr → PolyCnstr
  | .eq p₁ p₂ => .eq (p₁.toPoly.norm.sub p₂.toPoly)
  | .le p₁ p₂ => .le (p₁.toPoly.norm.sub p₂.toPoly)

attribute [local simp] Int.add_comm Int.add_assoc Int.add_left_comm Int.add_mul Int.mul_add
attribute [local simp] Poly.insert Poly.denote Poly.norm Poly.norm.go

theorem Poly.denote_insert (ctx : Context) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  induction p <;> simp
  next k' v' p' ih =>
    by_cases h₁ : Nat.blt v v' <;> simp [*]
    by_cases h₂ : Nat.beq v v' <;> simp [*]
    simp [Nat.eq_of_beq_eq_true h₂]

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm_go (ctx : Context) (p : Poly) (r : Poly) : (norm.go p r).denote ctx = p.denote ctx + r.denote ctx := by
  induction p generalizing r <;> simp [*]

attribute [local simp] Poly.denote_norm_go

theorem Poly.denote_norm (ctx : Context) (m : Poly) : m.norm.denote ctx = m.denote ctx := by
  simp

attribute [local simp] Poly.denote_norm Poly.sub

theorem Poly.denote_sub (ctx : Context) (p₁ p₂ : Poly) : (p₁.sub p₂).denote ctx = p₁.denote ctx - p₂.denote ctx := by
  induction p₂ generalizing p₁ <;> simp [*, ←Int.neg_mul]
  next k v p ih =>
    rw [Int.add_sub_assoc]
    conv => rhs; rw [Int.sub_eq_add_neg]
    apply congrArg
    rw [Int.add_comm, Int.neg_add, Int.neg_mul, Int.sub_eq_add_neg]

attribute [local simp] Poly.denote_sub
attribute [local simp] ExprCnstr.denote ExprCnstr.toPoly PolyCnstr.denote Expr.denote

theorem Expr.denote_toPoly_go (ctx : Context) (e : Expr) :
  (toPoly.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
    induction k, e using Expr.toPoly.go.induct generalizing p with
  | case1 k k' =>
    simp only [toPoly.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, Var.denote]
  | case2 k i => simp [toPoly.go]
  | case3 k a b iha ihb => simp [toPoly.go, iha, ihb]
  | case4 k k' a ih
  | case5 k a k' ih =>
    simp only [toPoly.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, cond_false, Int.mul_assoc]
      simp at ih
      rw [ih]
      rw [Int.mul_assoc, Int.mul_comm k']

theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  simp [toPoly, Expr.denote_toPoly_go]

attribute [local simp] Expr.denote_toPoly

theorem ExprCnstr.denote_toPoly (ctx : Context) (c : ExprCnstr) : c.toPoly.denote ctx = c.denote ctx := by
  cases c <;> simp
  · rw [Int.sub_eq_zero]
  · constructor
    · exact Int.le_of_sub_nonpos
    · exact Int.sub_nonpos_of_le

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all
    · simp! [BEq.beq]
    · simp! [BEq.beq]
    · rename_i k₁ v₁ p₁ ih k₂ v₂ p₂
      show (k₁ == k₂ && (v₁ == v₂ && p₁ == p₂)) = true → _
      simp +contextual
      intro _ _ h
      exact ih h
  rfl := by
    intro a
    induction a; rfl
    rename_i k v p ih
    show (k == k && (v == v && p == p)) = true
    simp_all

instance : LawfulBEq PolyCnstr where
  eq_of_beq {a b} := by
    cases a <;> cases b <;> rename_i p₁ p₂
    · show (p₁ == p₂) = true → _
      simp
    · simp! [BEq.beq]
    · simp! [BEq.beq]
    · show (p₁ == p₂) = true → _
      simp
  rfl {a} := by
    cases a <;> rename_i p <;> show (p == p) = true
      <;> simp

theorem Expr.eq_of_toNormPoly_eq (ctx : Context) (e e' : Expr) (h : e.toNormPoly == e'.toPoly) : e.denote ctx = e'.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Expr.toNormPoly, Poly.norm] at h
  assumption

theorem ExprCnstr.eq_of_toNormPoly_eq (ctx : Context) (c c' : ExprCnstr) (h : c.toPoly == c'.toPoly) : c.denote ctx = c'.denote ctx := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rw [denote_toPoly, denote_toPoly] at h
  assumption

end Int.Linear
