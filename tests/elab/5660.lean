import Lean


def ex : ∃ x : Nat, x = 1 :=
  ⟨1, rfl⟩

open Lean Meta

/--
error: invalid projection
  ex.3
from type
  ∃ x, x = 1
-/
#guard_msgs in
run_meta check (Expr.proj ``Exists 2 (mkConst ``ex)) -- should fail

/--
error: invalid projection
  ex.1
from type
  ∃ x, x = 1
-/
#guard_msgs in
run_meta check (Expr.proj ``Exists 0 (mkConst ``ex)) -- should fail

run_meta check (Expr.proj ``Exists 1 (mkConst ``ex))

def p := (1, 2)

/--
error: invalid projection
  p.1
from type
  Nat × Nat
-/
#guard_msgs in
run_meta check (Expr.proj ``Exists 0 (mkConst ``p)) -- should fail

run_meta check (Expr.proj ``Prod 0 (mkConst ``p))
run_meta check (Expr.proj ``Prod 1 (mkConst ``p))

/--
error: invalid projection
  p.3
from type
  Nat × Nat
-/
#guard_msgs in
run_meta check (Expr.proj ``Prod 2 (mkConst ``p)) -- should fail

def n := 1

/--
error: invalid projection
  n.1
from type
  Nat
-/
#guard_msgs in
run_meta check (Expr.proj ``Nat 0 (mkConst ``n)) -- should fail
