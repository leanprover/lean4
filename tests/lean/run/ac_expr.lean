import Std

inductive Expr (maxVarId : Nat) : Type where
  | var (i : Fin maxVarId)
  | op  (lhs rhs : Expr maxVarId)
  deriving Repr

def List.getIdx : (l : List α) → Fin l.length → α
  | [],    ⟨_, i⟩ => by
    simp [length] at i
    apply absurd i
    cases i
  | a::as, ⟨0, _⟩ => a
  | a::as, ⟨i+1, h⟩ => by
    apply getIdx as ⟨i, _⟩
    simp [List.length_cons] at h
    apply Nat.lt_of_succ_lt_succ
    assumption

structure Context (α : Type u) where
  op    : α → α → α
  assoc : (a b c : α) → op (op a b) c = op a (op b c)
  comm  : (a b : α) → op a b = op b a
  vars  : List α

theorem Context.left_comm (ctx : Context α) (a b c : α) : ctx.op a (ctx.op b c) = ctx.op b (ctx.op a c) := by
  rw [← ctx.assoc, ctx.comm a b, ctx.assoc]

def Expr.denote (ctx : Context α) : Expr ctx.vars.length → α
  | Expr.op a b => ctx.op (denote ctx a) (denote ctx b)
  | Expr.var i  => ctx.vars.getIdx i

theorem Expr.denote_op (ctx : Context α) (a b : Expr ctx.vars.length) : denote ctx (Expr.op a b) = ctx.op (denote ctx a) (denote ctx b) :=
  rfl

def Expr.concat : Expr n → Expr n → Expr n
  | Expr.op a b, c => Expr.op a (concat b c)
  | Expr.var i, c  => Expr.op (Expr.var i) c

theorem Expr.denote_concat (ctx : Context α) (a b : Expr ctx.vars.length) : denote ctx (concat a b) = denote ctx (Expr.op a b) := by
  induction a with
  | var i => rfl
  | op _ _ _ ih => simp [denote, ih, ctx.assoc]

def Expr.flat : Expr n → Expr n
  | Expr.op a b => concat (flat a) (flat b)
  | Expr.var i  => Expr.var i

theorem Expr.denote_flat (ctx : Context α) (e : Expr ctx.vars.length) : denote ctx (flat e) = denote ctx e := by
  induction e with
  | var i => rfl
  | op a b ih₁ ih₂ => simp [flat, denote, denote_concat, ih₁, ih₂]

theorem Expr.eq_of_flat (ctx : Context α) (a b : Expr ctx.vars.length) (h : flat a = flat b) : denote ctx a = denote ctx b := by
  have h := congrArg (denote ctx) h
  simp [denote_flat] at h
  assumption

def Expr.length : Expr n → Nat
  | op a b => 1 + b.length
  | _      => 1

def Expr.sort (e : Expr n) : Expr n :=
  loop e.length e
where
  loop : Nat → Expr n → Expr n
    | fuel+1, Expr.op a e =>
      let (e₁, e₂) := swap a e
      Expr.op e₁ (loop fuel e₂)
    | _, e => e

  swap : Expr n → Expr n → Expr n × Expr n
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

theorem Expr.denote_sort (ctx : Context α) (e : Expr ctx.vars.length) : denote ctx (sort e) = denote ctx e := by
  apply denote_loop
where
  denote_loop (n : Nat) (e : Expr ctx.vars.length) : denote ctx (sort.loop n e) = denote ctx e := by
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

  denote_swap (e₁ e₂ : Expr ctx.vars.length) : denote ctx (Expr.op (sort.swap e₁ e₂).1 (sort.swap e₁ e₂).2) = denote ctx (Expr.op e₁ e₂) := by
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

theorem Expr.eq_of_sort_flat (ctx : Context α) (a b : Expr ctx.vars.length) (h : sort (flat a) = sort (flat b)) : denote ctx a = denote ctx b := by
  have h := congrArg (denote ctx) h
  simp [denote_flat, denote_sort] at h
  assumption

theorem ex₁ (x₁ x₂ x₃ x₄ : Nat) : (x₁ + x₂) + (x₃ + x₄) = x₁ + x₂ + x₃ + x₄ :=
  Expr.eq_of_flat
    { op    := Nat.add
      assoc := Nat.add_assoc
      comm  := Nat.add_comm
      vars  := [x₁, x₂, x₃, x₄] }
    (Expr.op (Expr.op (Expr.var ⟨0, by simp⟩) (Expr.var ⟨1, by simp⟩)) (Expr.op (Expr.var ⟨2, by simp⟩) (Expr.var ⟨3, by simp⟩)))
    (Expr.op (Expr.op (Expr.op (Expr.var ⟨0, by simp⟩) (Expr.var ⟨1, by simp⟩)) (Expr.var ⟨2, by simp⟩)) (Expr.var ⟨3, by simp⟩))
    (by rfl)

theorem ex₂ (x₁ x₂ x₃ x₄ : Nat) : (x₁ + x₂) + (x₃ + x₄) = x₃ + x₁ + x₂ + x₄ :=
  Expr.eq_of_sort_flat
    { op    := Nat.add
      assoc := Nat.add_assoc
      comm  := Nat.add_comm
      vars  := [x₁, x₂, x₃, x₄] }
    (Expr.op (Expr.op (Expr.var ⟨0, by simp⟩) (Expr.var ⟨1, by simp⟩)) (Expr.op (Expr.var ⟨2, by simp⟩) (Expr.var ⟨3, by simp⟩)))
    (Expr.op (Expr.op (Expr.op (Expr.var ⟨2, by simp⟩) (Expr.var ⟨0, by simp⟩)) (Expr.var ⟨1, by simp⟩)) (Expr.var ⟨3, by simp⟩))
    (by rfl)

#print ex₂
