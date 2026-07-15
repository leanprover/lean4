/-!
This file contains tests for typical mistakes one might do when using `inductive_fixpoint`/`coinductive_fixpoint`/`partial_fixpoint` machinery, that is:
 - Try to use `coinductive_fixpoint`/`inductive_fixpoint` to define functions instead of predicates
 - Apply `coinductive_fixpoint`/`inductive_fixpoint` to non-recursive functions
 - Mix `partial_fixpoint` with `coinductive_fixpoint`/`inductive_fixpoint` in the same clique
-/

/--
error: `coinductive_fixpoint` can be only used to define predicates
-/
#guard_msgs in
def f (x : Nat) : Nat :=
  f (x + 1)
coinductive_fixpoint

/--
error: `inductive_fixpoint` can be only used to define predicates
-/
#guard_msgs in
def g (x : Nat) : Nat :=
  g (x + 1)
inductive_fixpoint

/--
warning: unused `coinductive_fixpoint`, function is not recursive
-/
#guard_msgs in
def h (x : Nat) : Prop := x > 42
  coinductive_fixpoint

/--
warning: unused `inductive_fixpoint`, function is not recursive
-/
#guard_msgs in
def h' (x : Nat) : Prop := x > 42
  inductive_fixpoint
