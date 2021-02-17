import Std

inductive Expr where
  | var (i : Nat)
  | op  (lhs rhs : Expr)
  deriving Inhabited, Repr

def List.getIdx : List α → Nat → α → α
  | [],    i,   u => u
  | a::as, 0,   u => a
  | a::as, i+1, u => getIdx as i u

structure Context (α : Type u) where
  op    : α → α → α
  unit  : α
  assoc : (a b c : α) → op (op a b) c = op a (op b c)
  comm  : (a b : α) → op a b = op b a
  vars  : List α

theorem Context.left_comm (ctx : Context α) (a b c : α) : ctx.op a (ctx.op b c) = ctx.op b (ctx.op a c) := by
  rw [← ctx.assoc, ctx.comm a b, ctx.assoc]

def Expr.denote (ctx : Context α) : Expr → α
  | Expr.op a b => ctx.op (denote ctx a) (denote ctx b)
  | Expr.var i  => ctx.vars.getIdx i ctx.unit

theorem Expr.denote_op (ctx : Context α) (a b : Expr) : denote ctx (Expr.op a b) = ctx.op (denote ctx a) (denote ctx b) :=
  rfl

def Expr.length : Expr → Nat
  | op a b => 1 + b.length
  | _      => 1

def Expr.sort (e : Expr) : Expr :=
  loop e.length e
where
  loop : Nat → Expr → Expr
  | fuel+1, Expr.op a e =>
    let (e₁, e₂) := swap a e
    Expr.op e₁ (loop fuel e₂)
  | _, e => e

  swap : Expr → Expr → Expr × Expr
  | Expr.var i, Expr.op (Expr.var j) e =>
    if i > j then
      let (e₁, e₂) := swap (Expr.var j) e
      (e₁, Expr.op (Expr.var i) e₂)
    else
      let (e₁, e₂) := swap (Expr.var i) e
      (e₁, Expr.op (Expr.var j) e₂)
  | Expr.var i, Expr.var j =>
    if i > j then
      (Expr.var j, Expr.var i)
    else
      (Expr.var i, Expr.var j)
  | e₁, e₂ => (e₁, e₂)

theorem Expr.denote_swap (ctx : Context α) (e₁ e₂ : Expr) : denote ctx (Expr.op (sort.swap e₁ e₂).1 (sort.swap e₁ e₂).2) = denote ctx (Expr.op e₁ e₂) := by
    induction e₂ generalizing e₁ with
    | op a b ih' ih =>
      cases e₁ with
      | var i =>
        have ih' := ih (var i)
        match h:sort.swap (var i) b with
        | (r₁, r₂) =>
          rw [denote_op _ (var i)] at ih'
          admit
      | _ => admit
    | _ => admit
