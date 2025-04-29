/-!
This file contains tests for typical mistakes one might do when using `least_fixpoint`/`greatest_fixpoint`/`partial_fixpoint` machinery, that is:
 - Try to use `greatest_fixpoint`/`least_fixpoint` to define functions instead of predicates
 - Mix `partial_fixpoint` with `greatest_fixpoint`/`least_fixpoint` in the same clique
 - Apply `greatest_fixpoint`/`least_fixpoint` to non-recursive functions
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

/--
error: all functions in the clique must be defined using lattice theory, but some are not
-/
#guard_msgs in
mutual
  def f₁ (x : Nat) : Prop :=
    g₁  (x + 1)
  partial_fixpoint
  def g₁ (x : Nat) : Prop := f₁ (x + 1)
  least_fixpoint
end

-- Only lattice-theoretic fixpoints in the clique are fine
mutual
  def f₂ (x : Nat) : Prop :=
    g₂ (x + 1)
  least_fixpoint

  def g₂ (x : Nat) : Prop := f₂ (x + 1)
  least_fixpoint
end

/--
error: all functions in the clique must be defined using lattice theory, but some are not
-/
#guard_msgs in
mutual
  def f₃ (x : Nat) : Prop :=
    g₃ (x + 1)
  greatest_fixpoint

  def g₃ (x : Nat) : Prop := f₃ (x + 1)
  partial_fixpoint
end


-- Only `partial_fixpoint` definitions in the clique are also fine
mutual
  def f₄ (x : Nat) : Prop :=
    g₄ (x + 1)
  partial_fixpoint

  def g₄ (x : Nat) : Prop := f₄ (x + 1)
  partial_fixpoint
end
