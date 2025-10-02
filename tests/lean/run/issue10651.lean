-- set_option trace.Elab.definition.eqns true

def f (x : Nat) : Nat :=
  match x with
  | 0    => 1
  | 100  => 2
  | 1000 => 3
  | x+1  => f x
termination_by x

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs(pass trace, all) in
#print equations f

def g (x : Nat) : Nat :=
  match x with
  | 0    => 1
  | 100  => 2
  | 1000 => 3
  | x+1  => x

/--
info: equations:
@[defeq] theorem g.eq_1 : g 0 = 1
@[defeq] theorem g.eq_2 : g 100 = 2
@[defeq] theorem g.eq_3 : g 1000 = 3
theorem g.eq_4 : ∀ (x_2 : Nat), (x_2 = 99 → False) → (x_2 = 999 → False) → g x_2.succ = x_2
-/
#guard_msgs(pass trace, all) in
#print equations g
