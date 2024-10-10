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

set_option trace.Elab.definition.structural.eqns true
set_option trace.Elab.definition.wf.eqns true

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

#check optimize2.eq_2
