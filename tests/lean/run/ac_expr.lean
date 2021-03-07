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

def Expr.concat : Expr → Expr → Expr
  | Expr.op a b, c => Expr.op a (concat b c)
  | Expr.var i, c  => Expr.op (Expr.var i) c

theorem Expr.denote_concat (ctx : Context α) (a b : Expr) : denote ctx (concat a b) = denote ctx (Expr.op a b) := by
  induction a with
  | var i => rfl
  | op _ _ _ ih => simp [denote, ih, ctx.assoc]

def Expr.flat : Expr → Expr
  | Expr.op a b => concat (flat a) (flat b)
  | Expr.var i  => Expr.var i

theorem Expr.denote_flat (ctx : Context α) (e : Expr) : denote ctx (flat e) = denote ctx e := by
  induction e with
  | var i => rfl
  | op a b ih₁ ih₂ => simp [flat, denote, denote_concat, ih₁, ih₂]

theorem Expr.eq_of_flat (ctx : Context α) (a b : Expr) (h : flat a = flat b) : denote ctx a = denote ctx b := by
  have h := congrArg (denote ctx) h
  simp [denote_flat] at h
  assumption

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

theorem Expr.denote_sort (ctx : Context α) (e : Expr) : denote ctx (sort e) = denote ctx e := by
  apply denote_loop
where
  denote_loop (n : Nat) (e : Expr) : denote ctx (sort.loop n e) = denote ctx e := by
    induction n generalizing e with
    | zero => rfl
    | succ n ih =>
      match e with
      | var _  => rfl
      | op a b =>
        simp [denote, sort.loop]
        match h:sort.swap a b with
        | (r₁, r₂) =>
          have hs := denote_swap a b
          rw [h] at hs
          simp [denote] at hs
          simp [denote, ih]
          assumption

  denote_swap (e₁ e₂ : Expr) : denote ctx (Expr.op (sort.swap e₁ e₂).1 (sort.swap e₁ e₂).2) = denote ctx (Expr.op e₁ e₂) := by
    induction e₂ generalizing e₁ with
    | op a b ih' ih =>
      clear ih'
      cases e₁ with
      | var i =>
        cases a with
        | var j =>
          byCases h : i > j
          focus
            simp [sort.swap, h]
            match h:sort.swap (var j) b with
            | (r₁, r₂) => simp; rw [denote_op (a := var i), ← ih]; simp [h, denote]; rw [Context.left_comm]
          focus
            simp [sort.swap, h]
            match h:sort.swap (var i) b with
            | (r₁, r₂) =>
              simp
              rw [denote_op (a := var i), denote_op (a := var j), Context.left_comm, ← denote_op (a := var i), ← ih]
              simp [h, denote]
              rw [Context.left_comm]
        | _ => rfl
      | _ => rfl
    | var j =>
      cases e₁ with
      | var i =>
        byCases h : i > j
        focus simp [sort.swap, h, denote, Context.comm]
        focus simp [sort.swap, h]
      | _ => rfl

theorem Expr.eq_of_sort_flat (ctx : Context α) (a b : Expr) (h : sort (flat a) = sort (flat b)) : denote ctx a = denote ctx b := by
  have h := congrArg (denote ctx) h
  simp [denote_flat, denote_sort] at h
  assumption

theorem ex₁ (x₁ x₂ x₃ x₄ : Nat) : (x₁ + x₂) + (x₃ + x₄) = x₁ + x₂ + x₃ + x₄ :=
  Expr.eq_of_flat
    { op    := Nat.add
      assoc := Nat.add_assoc
      comm  := Nat.add_comm
      unit  := Nat.zero
      vars  := [x₁, x₂, x₃, x₄] }
    (Expr.op (Expr.op (Expr.var 0) (Expr.var 1)) (Expr.op (Expr.var 2) (Expr.var 3)))
    (Expr.op (Expr.op (Expr.op (Expr.var 0) (Expr.var 1)) (Expr.var 2)) (Expr.var 3))
    rfl

theorem ex₂ (x₁ x₂ x₃ x₄ : Nat) : (x₁ + x₂) + (x₃ + x₄) = x₃ + x₁ + x₂ + x₄ :=
  Expr.eq_of_sort_flat
    { op    := Nat.add
      assoc := Nat.add_assoc
      comm  := Nat.add_comm
      unit  := Nat.zero
      vars  := [x₁, x₂, x₃, x₄] }
    (Expr.op (Expr.op (Expr.var 0) (Expr.var 1)) (Expr.op (Expr.var 2) (Expr.var 3)))
    (Expr.op (Expr.op (Expr.op (Expr.var 2) (Expr.var 0)) (Expr.var 1)) (Expr.var 3))
    rfl

#print ex₂
