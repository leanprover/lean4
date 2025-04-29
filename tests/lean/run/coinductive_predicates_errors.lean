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
error: Invalid `termination_by`; this function is mutually recursive with f₁, which is marked as `partial_fixpoint` so this one also needs to be marked `partial_fixpoint`.
-/
#guard_msgs in
mutual
  def f₁ (x : Nat) : Prop :=
    g₁  (x + 1)
  partial_fixpoint
  def g₁ (x : Nat) : Prop := f₁ (x + 1)
  least_fixpoint
end

-- Only `least_fixpoint`/`greatest_fixpoint` in the clique are fine
mutual
  def f₂ (x : Nat) : Prop :=
    g₂ (x + 1)
  least_fixpoint

  def g₂ (x : Nat) : Prop := f₂ (x + 1)
  least_fixpoint
end

/--
error: Invalid `termination_by`; this function is mutually recursive with f₃, which is marked as `greatest_fixpoint` so this one also needs to be marked `least_fixpoint` or `greatest_fixpoint`.
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

/--
error: Invalid `termination_by`; this function is mutually recursive with f₅, which is not also marked as `partial_fixpoint`, so this one cannot be either.
-/
#guard_msgs in
mutual
  def f₅ (x : Nat) : Prop :=
    g₅ (x + 1)
    termination_by?

  def g₅ (x : Nat) : Prop :=
    f₅ (x + 1)
    partial_fixpoint
end

/--
error: Invalid `termination_by`; this function is mutually recursive with f₆, which is not also marked as `least_fixpoint` or `greatest_fixpoint`, so this one cannot be either.
-/
#guard_msgs in
mutual
  def f₆ (x : Nat) : Prop :=
    g₆ (x + 1)
    termination_by?

  def g₆ (x : Nat) : Prop :=
    f₆ (x + 1)
    least_fixpoint
end

/--
error: Invalid `termination_by`; this function is mutually recursive with f₇, which is marked as `greatest_fixpoint` so this one also needs to be marked `least_fixpoint` or `greatest_fixpoint`.
-/
#guard_msgs in
mutual
  def f₇ (x : Nat) : Prop :=
    g₇ (x + 1)
    greatest_fixpoint

  def g₇ (x : Nat) : Prop :=
    f₇ (x + 1)
    termination_by?
end

/--
error: Invalid `termination_by`; this function is mutually recursive with f₈, which is marked as `partial_fixpoint` so this one also needs to be marked `partial_fixpoint`.
-/
#guard_msgs in
mutual
  def f₈ (x : Nat) : Prop :=
    g₈ (x +1)
    partial_fixpoint

  def g₈ (x : Nat) : Prop :=
    f₈ (x + 1)
end
