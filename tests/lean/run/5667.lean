inductive Expr where
  | const (i : BitVec 32)
  | op (op : Unit) (e1 : Expr)

def optimize : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match bop, optimize e1 with
    | _, .const _ => .op bop (.const 0)
    | _, _ => .const 0

/--
error: Failed to realize constant optimize.eq_def:
  failed to generate equational theorem for 'optimize'
  case h_2
  e1 : Expr
  i : BitVec 32
  heq : optimize e1 = Expr.const i
  bop✝ bop_1 : Unit
  x : Expr
  x_3 :
    ∀ (i : BitVec 32),
      (Expr.rec (fun i => ⟨Expr.const i, PUnit.unit⟩)
              (fun op e1 e1_ih =>
                ⟨match op, e1_ih.1 with
                  | x, Expr.const i => Expr.op op (Expr.const 0)
                  | x, x_1 => Expr.const 0,
                  e1_ih⟩)
              e1).1 =
          Expr.const i →
        False
  ⊢ Expr.const 0 = Expr.op bop✝ (Expr.const 0)
---
error: Failed to realize constant optimize.eq_def:
  failed to generate equational theorem for 'optimize'
  case h_2
  e1 : Expr
  i : BitVec 32
  heq : optimize e1 = Expr.const i
  bop✝ bop_1 : Unit
  x : Expr
  x_3 :
    ∀ (i : BitVec 32),
      (Expr.rec (fun i => ⟨Expr.const i, PUnit.unit⟩)
              (fun op e1 e1_ih =>
                ⟨match op, e1_ih.1 with
                  | x, Expr.const i => Expr.op op (Expr.const 0)
                  | x, x_1 => Expr.const 0,
                  e1_ih⟩)
              e1).1 =
          Expr.const i →
        False
  ⊢ Expr.const 0 = Expr.op bop✝ (Expr.const 0)
---
error: unknown identifier 'optimize.eq_def'
-/
#guard_msgs in
#check optimize.eq_def

/--
error: failed to generate equational theorem for 'optimize'
case h_2
e1 : Expr
i : BitVec 32
heq : optimize e1 = Expr.const i
bop✝ bop_1 : Unit
x : Expr
x_3 :
  ∀ (i : BitVec 32),
    (Expr.rec (fun i => ⟨Expr.const i, PUnit.unit⟩)
            (fun op e1 e1_ih =>
              ⟨match op, e1_ih.1 with
                | x, Expr.const i => Expr.op op (Expr.const 0)
                | x, x_1 => Expr.const 0,
                e1_ih⟩)
            e1).1 =
        Expr.const i →
      False
⊢ Expr.const 0 = Expr.op bop✝ (Expr.const 0)
-/
#guard_msgs in
#print equations optimize

-- works:

def optimize2 : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match optimize2 e1 with
    | .const _ => .op bop (.const 0)
    | _ => .const 0

/--
info: equations:
theorem optimize2.eq_1 : ∀ (i : BitVec 32), optimize2 (Expr.const i) = Expr.const i
theorem optimize2.eq_2 : ∀ (bop : Unit) (e1 : Expr),
  optimize2 (Expr.op bop e1) =
    match optimize2 e1 with
    | Expr.const i => Expr.op bop (Expr.const 0)
    | x => Expr.const 0
-/
#guard_msgs in
#print equations optimize2

-- also works:

def optimize3 : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match bop, e1 with
    | _, .const _ => .op bop (optimize3 e1)
    | _, _ => .const 0

/--
info: equations:
theorem optimize3.eq_1 : ∀ (i : BitVec 32), optimize3 (Expr.const i) = Expr.const i
theorem optimize3.eq_2 : ∀ (bop : Unit) (i : BitVec 32),
  optimize3 (Expr.op bop (Expr.const i)) = Expr.op bop (optimize3 (Expr.const i))
theorem optimize3.eq_3 : ∀ (bop : Unit) (e1 : Expr),
  (∀ (i : BitVec 32), e1 = Expr.const i → False) → optimize3 (Expr.op bop e1) = Expr.const 0
-/
#guard_msgs in
#print equations optimize3
