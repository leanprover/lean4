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

def Var.denote (ctx : Context) (v : Var) : Int :=
  ctx.get v

inductive Expr where
  | num  (v : Int)
  | var  (i : Var)
  | add  (a b : Expr)
  | sub  (a b : Expr)
  | mulL (k : Int) (a : Expr)
  | mulR (a : Expr) (k : Int)
  deriving Inhabited

def Expr.denote (ctx : Context) : Expr → Int
  | .add a b  => Int.add (denote ctx a) (denote ctx b)
  | .sub a b  => Int.sub (denote ctx a) (denote ctx b)
  | .num k    => k
  | .var v    => v.denote ctx
  | .mulL k e => Int.mul k (denote ctx e)
  | .mulR e k => Int.mul (denote ctx e) k

inductive Poly where
  | num (k : Int)
  | add (k : Int) (v : Var) (p : Poly)
  deriving BEq, Repr

def Poly.denote (ctx : Context) (p : Poly) : Int :=
  match p with
  | .num k => k
  | .add k v p => Int.add (Int.mul k (v.denote ctx)) (denote ctx p)

def Poly.addConst (p : Poly) (k : Int) : Poly :=
  match p with
  | .num k' => .num (k+k')
  | .add k' v' p => .add k' v' (addConst p k)

def Poly.insert (k : Int) (v : Var) (p : Poly) : Poly :=
  match p with
  | .num k' => .add k v (.num k')
  | .add k' v' p =>
    bif Nat.blt v v' then
      .add k v <| .add k' v' p
    else bif Nat.beq v v' then
      if Int.add k k' == 0 then
        p
      else
        .add (Int.add k k') v' p
    else
      .add k' v' (insert k v p)

def Poly.norm (p : Poly) : Poly :=
  match p with
  | .num k => .num k
  | .add k v p => (norm p).insert k v

def Expr.toPoly' (e : Expr) :=
  go 1 e (.num 0)
where
  go (coeff : Int) : Expr → (Poly → Poly)
    | .num k    => bif k == 0 then id else (Poly.addConst · (Int.mul coeff k))
    | .var v    => (.add coeff v ·)
    | .add a b  => go coeff a ∘ go coeff b
    | .sub a b  => go coeff a ∘ go (-coeff) b
    | .mulL k a
    | .mulR a k => bif k == 0 then id else go (Int.mul coeff k) a

def Expr.toPoly (e : Expr) : Poly :=
  e.toPoly'.norm

inductive PolyCnstr  where
  | eq (p : Poly)
  | le (p : Poly)
  deriving BEq, Repr

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
  | .eq e₁ e₂ => e₁.denote ctx = e₂.denote ctx
  | .le e₁ e₂ => e₁.denote ctx ≤ e₂.denote ctx

def ExprCnstr.toPoly : ExprCnstr → PolyCnstr
  | .eq e₁ e₂ => .eq (e₁.sub e₂).toPoly.norm
  | .le e₁ e₂ => .le (e₁.sub e₂).toPoly.norm

attribute [local simp] Int.add_comm Int.add_assoc Int.add_left_comm Int.add_mul Int.mul_add
attribute [local simp] Poly.insert Poly.denote Poly.norm Poly.addConst

theorem Poly.denote_addConst (ctx : Context) (p : Poly) (k : Int) : (p.addConst k).denote ctx = p.denote ctx + k := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_addConst

theorem Poly.denote_insert (ctx : Context) (k : Int) (v : Var) (p : Poly) :
    (p.insert k v).denote ctx = p.denote ctx + k * v.denote ctx := by
  induction p <;> simp [*]
  next k' v' p' ih =>
    by_cases h₁ : Nat.blt v v' <;> simp [*]
    by_cases h₂ : Nat.beq v v' <;> simp [*]
    by_cases h₃ : k + k' = 0 <;> simp [*, Nat.eq_of_beq_eq_true h₂]
    rw [← Int.add_mul]
    simp [*]

attribute [local simp] Poly.denote_insert

theorem Poly.denote_norm (ctx : Context) (p : Poly) : p.norm.denote ctx = p.denote ctx := by
  induction p <;> simp [*]

attribute [local simp] Poly.denote_norm

private theorem sub_fold (a b : Int) : a.sub b = a - b := rfl

attribute [local simp] sub_fold
attribute [local simp] ExprCnstr.denote ExprCnstr.toPoly PolyCnstr.denote Expr.denote

theorem Expr.denote_toPoly'_go (ctx : Context) (e : Expr) :
  (toPoly'.go k e p).denote ctx = k * e.denote ctx + p.denote ctx := by
    induction k, e using Expr.toPoly'.go.induct generalizing p with
  | case1 k k' =>
    simp only [toPoly'.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, Var.denote]
  | case2 k i => simp [toPoly'.go]
  | case3 k a b iha ihb => simp [toPoly'.go, iha, ihb]
  | case4 k a b iha ihb =>
    simp [toPoly'.go, iha, ihb, Int.mul_sub]
    rw [Int.sub_eq_add_neg, ←Int.neg_mul, Int.add_assoc]
  | case5 k k' a ih
  | case6 k a k' ih =>
    simp only [toPoly'.go]
    by_cases h : k' == 0
    · simp [h, eq_of_beq h]
    · simp [h, cond_false, Int.mul_assoc]
      simp at ih
      rw [ih]
      rw [Int.mul_assoc, Int.mul_comm k']

theorem Expr.denote_toPoly (ctx : Context) (e : Expr) : e.toPoly.denote ctx = e.denote ctx := by
  simp [toPoly, toPoly', Expr.denote_toPoly'_go]

attribute [local simp] Expr.denote_toPoly

theorem ExprCnstr.denote_toPoly (ctx : Context) (c : ExprCnstr) : c.toPoly.denote ctx = c.denote ctx := by
  cases c <;> simp
  · rw [Int.sub_eq_zero]
  · constructor
    · exact Int.le_of_sub_nonpos
    · exact Int.sub_nonpos_of_le

instance : LawfulBEq Poly where
  eq_of_beq {a} := by
    induction a <;> intro b <;> cases b <;> simp_all! [BEq.beq]
    · rename_i k₁ v₁ p₁ k₂ v₂ p₂ ih
      intro _ _ h
      exact ih h
  rfl := by
    intro a
    induction a <;> simp! [BEq.beq]
    · rename_i k v p ih
      exact ih

instance : LawfulBEq PolyCnstr where
  eq_of_beq {a b} := by
    cases a <;> cases b <;> rename_i p₁ p₂ <;> simp_all! [BEq.beq]
    · show (p₁ == p₂) = true → _
      simp
    · show (p₁ == p₂) = true → _
      simp
  rfl {a} := by
    cases a <;> rename_i p <;> show (p == p) = true
      <;> simp

theorem Expr.eq_of_toPoly_eq (ctx : Context) (e e' : Expr) (h : e.toPoly == e'.toPoly) : e.denote ctx = e'.denote ctx := by
  have h := congrArg (Poly.denote ctx) (eq_of_beq h)
  simp [Poly.norm] at h
  assumption

theorem ExprCnstr.eq_of_toPoly_eq (ctx : Context) (c c' : ExprCnstr) (h : c.toPoly == c'.toPoly) : c.denote ctx = c'.denote ctx := by
  have h := congrArg (PolyCnstr.denote ctx) (eq_of_beq h)
  rw [denote_toPoly, denote_toPoly] at h
  assumption

end Int.Linear
