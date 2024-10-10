inductive Expr where
  | const (i : BitVec 32)
  | op (op : Unit) (e1 : Expr)

-- fails:

def optimize : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match bop, optimize e1 with
    | _, .const _ => .op bop (.const 0)
    | _, _ => .const 0
termination_by structural e => e

/--
info: optimize.eq_def :
  ∀ (x : Expr),
    optimize x =
      match x with
      | Expr.const i => Expr.const i
      | Expr.op bop e1 =>
        match bop, optimize e1 with
        | x, Expr.const i => Expr.op bop (Expr.const 0)
        | x, x_1 => Expr.const 0
-/
#guard_msgs in
#check optimize.eq_def


/--
info: optimize.eq_2 (e1 : Expr) :
  ∀ (bop : Unit) (i : BitVec 32), optimize e1 = Expr.const i → optimize (Expr.op bop e1) = Expr.op bop (Expr.const 0)
-/
#guard_msgs in
#check optimize.eq_2

def optimize2 : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match bop, optimize2 e1 with
    | _, .const _ => .op bop (.const 0)
    | _, _ => .const 0
termination_by e => e

set_option trace.Elab.definition.structural.eqns true
set_option trace.Elab.definition.wf.eqns true

#check optimize2.eq_unfold
#check optimize2.eq_2
