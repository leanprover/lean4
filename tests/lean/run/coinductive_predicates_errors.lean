/-!
This file contains tests for typical mistakes one might do when using `least_fixpoint`/`greatest_fixpoint`/`partial_fixpoint` machinery, that is:
 - Try to use `greatest_fixpoint`/`least_fixpoint` to define functions instead of predicates
 - Apply `greatest_fixpoint`/`least_fixpoint` to non-recursive functions
 - Mix `partial_fixpoint` with `greatest_fixpoint`/`least_fixpoint` in the same clique
-/

/--
error: `greatest_fixpoint` can be only used to define predicates
-/
#guard_msgs in
def f (x : Nat) : Nat :=
  f (x + 1)
greatest_fixpoint

/--
error: `least_fixpoint` can be only used to define predicates
-/
#guard_msgs in
def g (x : Nat) : Nat :=
  g (x + 1)
least_fixpoint

/--
warning: unused `greatest_fixpoint`, function is not recursive
-/
#guard_msgs in
def h (x : Nat) : Prop := x > 42
  greatest_fixpoint

/--
warning: unused `least_fixpoint`, function is not recursive
-/
#guard_msgs in
def h' (x : Nat) : Prop := x > 42
  least_fixpoint
