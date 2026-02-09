
def foo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => foo n
termination_by structural n

-- Test that this is indeed by structural recursion
example : foo (n + 3) = foo n := Eq.refl _


-- Check that we can still refer to a variable called `structural` in
-- the `termination_by` syntax
def bar (structural : Nat) : True := match structural with
  | 0 => .intro
  | structural+1 => bar structural
termination_by «structural»

namespace Errors
-- A few error conditions

/--
error: cannot use specified measure for structural recursion:
  it is unchanged in the recursive calls
-/
#guard_msgs in
def foo1 (n : Nat) : Nat := foo1 n
termination_by structural n

/--
error: cannot use specified measure for structural recursion:
  its type Nat.le is an inductive family and indices are not variables
    n.succ.le 100
-/
#guard_msgs in
def foo2 (n : Nat) (h : n < 100) : Nat := match n with
  | 0 => 0
  | n+1 => foo2 n (by omega)
termination_by structural h

/--
error: one parameter bound in `termination_by`, but the body of Errors.foo3 only binds 0 parameters.
-/
#guard_msgs in
def foo3 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo3 n
termination_by structural m => m

/--
error: failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    ackermann (n + 1) m
-/
#guard_msgs in
def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
termination_by structural n

/--
error: failed to infer structural recursion:
Cannot use parameter m:
  failed to eliminate recursive application
    ackermann2 n 1
-/
#guard_msgs in
def ackermann2 (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann2 n 1
  | .succ n, .succ m => ackermann2 n (ackermann2 (n + 1) m)
termination_by structural m

/--
error: The termination measure of a structurally recursive function must be one of the parameters 'n', but
  id n + 1
isn't one of these.
-/
#guard_msgs in
def foo4 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo4 n
termination_by structural id n + 1

/--
error: failed to infer structural recursion:
Cannot use parameter #2:
  the type Nat × Nat does not have a `.brecOn` recursor
-/
#guard_msgs in
def foo5 : Nat → (Nat × Nat) → Nat
 | 0, _ => 0
 | n+1, t => foo5 n t
termination_by structural n t => t

/--
error: failed to infer structural recursion:
Cannot use parameters #2 of Errors.foo6 and #2 of Errors.bar6:
  the type Nat × Nat does not have a `.brecOn` recursor
-/
#guard_msgs in
mutual
def foo6 : Nat → (Nat × Nat) → Nat
 | 0, _ => 0
 | n+1, t => bar6 n t
termination_by structural n t => t
def bar6 : Nat → (Nat × Nat) → Nat
 | 0, _ => 0
 | n+1, t => foo6 n t
termination_by structural n t => t
end

end Errors
