import Std

inductive Expr where
  | var (i : Nat)
  | op  (lhs rhs : Expr)

def List.getIdx : List α → Nat → α → α
  | [],    i,   u => u
  | a::as, 0,   u => a
  | a::as, i+1, u => getIdx as i u

structure Context (α : Type u) where
  op    : α → α → α
  unit  : α
  assoc : (a b c : α) → op (op a b) c = op a (op b c)
  vars  : List α

def Expr.denote (ctx : Context α) : Expr → α
  | Expr.op a b => ctx.op (denote ctx a) (denote ctx b)
  | Expr.var i  => ctx.vars.getIdx i ctx.unit

theorem Expr.denote_op (ctx : Context α) (a b : Expr) : denote ctx (Expr.op a b) = ctx.op (denote ctx a) (denote ctx b) :=
  rfl

theorem Expr.denote_var (ctx : Context α) (i : Nat) : denote ctx (Expr.var i) = ctx.vars.getIdx i ctx.unit :=
  rfl

def Expr.concat : Expr → Expr → Expr
  | Expr.op a b, c => Expr.op a (concat b c)
  | Expr.var i, c  => Expr.op (Expr.var i) c

theorem Expr.concat_op (a b c : Expr) : concat (Expr.op a b) c = Expr.op a (concat b c) :=
  rfl

theorem Expr.concat_var (i : Nat) (c : Expr) : concat (Expr.var i) c = Expr.op (Expr.var i) c :=
  rfl

theorem Expr.denote_concat (ctx : Context α) (a b : Expr) : denote ctx (concat a b) = denote ctx (Expr.op a b) := by
  induction a with
  | var i => rfl
  | op _ _ _ ih => rw [concat_op, denote_op, ih, denote_op, denote_op, denote_op, ctx.assoc]

def Expr.flat : Expr → Expr
  | Expr.op a b => concat (flat a) (flat b)
  | Expr.var i  => Expr.var i

theorem Expr.flat_op (a b : Expr) : flat (Expr.op a b) = concat (flat a) (flat b) :=
  rfl

theorem Expr.denote_flat (ctx : Context α) (a : Expr) : denote ctx (flat a) = denote ctx a := by
  induction a with
  | var i => rfl
  | op a b ih₁ ih₂ => rw [flat_op, denote_concat, denote_op, denote_op, ih₁, ih₂]

theorem Expr.eq_of_flat (ctx : Context α) (a b : Expr) (h : flat a = flat b) : denote ctx a = denote ctx b := by
  rw [← Expr.denote_flat _ a, ← Expr.denote_flat _ b, h]

theorem test (x₁ x₂ x₃ x₄ : Nat) : (x₁ + x₂) + (x₃ + x₄) = x₁ + x₂ + x₃ + x₄ :=
  Expr.eq_of_flat
    { op    := Nat.add
      assoc := Nat.add_assoc
      unit  := Nat.zero
      vars  := [x₁, x₂, x₃, x₄] }
    (Expr.op (Expr.op (Expr.var 0) (Expr.var 1)) (Expr.op (Expr.var 2) (Expr.var 3)))
    (Expr.op (Expr.op (Expr.op (Expr.var 0) (Expr.var 1)) (Expr.var 2)) (Expr.var 3))
    rfl
