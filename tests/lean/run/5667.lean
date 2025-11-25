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
info: optimize.eq_def (x✝ : Expr) :
  optimize x✝ =
    match x✝ with
    | Expr.const i => Expr.const i
    | Expr.op bop e1 =>
      match bop, optimize e1 with
      | x, Expr.const i => Expr.op bop (Expr.const 0)
      | x, x_1 => Expr.const 0
-/
#guard_msgs in
#check optimize.eq_def

/--
info: equations:
@[defeq] theorem optimize.eq_1 : ∀ (i : BitVec 32), optimize (Expr.const i) = Expr.const i
theorem optimize.eq_2 : ∀ (e1 : Expr) (bop : Unit) (i : BitVec 32),
  optimize e1 = Expr.const i → optimize (Expr.op bop e1) = Expr.op bop (Expr.const 0)
theorem optimize.eq_3 : ∀ (e1 : Expr) (bop : Unit),
  (∀ (i : BitVec 32), optimize e1 = Expr.const i → False) → optimize (Expr.op bop e1) = Expr.const 0
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
@[defeq] theorem optimize2.eq_1 : ∀ (i : BitVec 32), optimize2 (Expr.const i) = Expr.const i
@[defeq] theorem optimize2.eq_2 : ∀ (bop : Unit) (e1 : Expr),
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
@[defeq] theorem optimize3.eq_1 : ∀ (i : BitVec 32), optimize3 (Expr.const i) = Expr.const i
@[defeq] theorem optimize3.eq_2 : ∀ (bop : Unit) (i : BitVec 32),
  optimize3 (Expr.op bop (Expr.const i)) = Expr.op bop (optimize3 (Expr.const i))
theorem optimize3.eq_3 : ∀ (bop : Unit) (e1 : Expr),
  (∀ (i : BitVec 32), e1 = Expr.const i → False) → optimize3 (Expr.op bop e1) = Expr.const 0
-/
#guard_msgs in
#print equations optimize3


-- Mutual

namespace Mutual

mutual
inductive Expr where
  | const (i : BitVec 32)
  | op (op : Unit) (e1 : Expr')
inductive Expr' where
  | const (i : BitVec 32)
  | op (op : Unit) (e1 : Expr)
end

mutual
def optimize : Expr → Expr
  | .const i => .const i
  | .op bop e1 =>
    match bop, optimize' e1 with
    | _, .const _ => .op bop (.const 0)
    | _, _ => .const 0
def optimize' : Expr' → Expr'
  | .const i => .const i
  | .op bop e1 =>
    match bop, optimize e1 with
    | _, .const _ => .op bop (.const 0)
    | _, _ => .const 0
end

/--
info: Mutual.optimize.eq_def (x✝ : Expr) :
  optimize x✝ =
    match x✝ with
    | Expr.const i => Expr.const i
    | Expr.op bop e1 =>
      match bop, optimize' e1 with
      | x, Expr'.const i => Expr.op bop (Expr'.const 0)
      | x, x_1 => Expr.const 0
-/
#guard_msgs in
#check optimize.eq_def
/--
info: Mutual.optimize'.eq_def (x✝ : Expr') :
  optimize' x✝ =
    match x✝ with
    | Expr'.const i => Expr'.const i
    | Expr'.op bop e1 =>
      match bop, optimize e1 with
      | x, Expr.const i => Expr'.op bop (Expr.const 0)
      | x, x_1 => Expr'.const 0
-/
#guard_msgs in
#check optimize'.eq_def

end Mutual
