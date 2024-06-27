
def foo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => foo n
termination_by structurally n

-- Test that this is indeed by structural recursion
example : foo (n + 3) = foo n := Eq.refl _


-- Check that we can still refer to a variable called `structurally` in
-- the `termination_by` syntax
def bar (structurally : Nat) : True := match structurally with
  | 0 => .intro
  | structurally+1 => bar structurally
termination_by «structurally»

namespace Errors
-- A few error conditions

/--
error: argument #1 cannot be used for structural recursion
  it is unchanged in the recursive calls
-/
#guard_msgs in
def foo1 (n : Nat) : Nat := foo1 n
termination_by structurally n

/--
error: argument #2 cannot be used for structural recursion
  its type is an inductive family and indices are not variables
    n.succ.le 100
-/
#guard_msgs in
def foo2 (n : Nat) (h : n < 100) : Nat := match n with
  | 0 => 0
  | n+1 => foo2 n (by omega)
termination_by structurally h

/--
error: one parameter bound in `termination_by`, but the body of Errors.foo3 only binds 0 parameters.
-/
#guard_msgs in
def foo3 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo3 n
termination_by structurally m => m

/--
error: argument #1 cannot be used for structural recursion
  failed to eliminate recursive application
    ackermann (n + 1) m
-/
#guard_msgs in
def ackermann (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann n 1
  | .succ n, .succ m => ackermann n (ackermann (n + 1) m)
termination_by structurally n

/--
error: argument #2 cannot be used for structural recursion
  failed to eliminate recursive application
    ackermann2 n 1
-/
#guard_msgs in
def ackermann2 (n m : Nat) := match n, m with
  | 0, m => m + 1
  | .succ n, 0 => ackermann2 n 1
  | .succ n, .succ m => ackermann2 n (ackermann2 (n + 1) m)
termination_by structurally m

/--
error: The termination argument of a structurally recursive function must be one of the parameters 'n', but
  id n + 1
isn't one of these.
-/
#guard_msgs in
def foo4 (n : Nat) : Nat → Nat := match n with
  | 0 => id
  | n+1 => foo4 n
termination_by structurally id n + 1


end Errors

namespace MutualIndNonMutualFun

mutual
inductive A
  | self : A → A
  | other : B → A
  | empty
inductive B
  | self : B → B
  | other : A → B
  | empty
end

/--
error: argument #1 cannot be used for structural recursion
  application type mismatch
    @A.brecOn (fun x => Nat) x✝
  argument
    x✝
  has type
    A : Type
  but is expected to have type
    B → Type : Type 1
-/
#guard_msgs in
def A.self_size : A → Nat
  | .self a => a.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

/--
error: argument #1 cannot be used for structural recursion
  application type mismatch
    @B.brecOn fun x => Nat
  argument
    fun x => Nat
  has type
    B → Type : Type 1
  but is expected to have type
    A → Type : Type 1
-/
#guard_msgs in
def B.self_size : B → Nat
  | .self b => b.self_size + 1
  | .other _ => 0
  | .empty => 0
termination_by structurally x => x

mutual
def A.size : A → Nat
  | .self a => a.size + 1
  | .other b => b.size + 1
  | .empty => 0
termination_by structurally x => x
def B.size : B → Nat
  | .self b => b.size + 1
  | .other a => a.size + 1
  | .empty => 0
termination_by structurally x => x
end

theorem A_size_eq1 (a : A) : (A.self a).size = a.size + 1 := rfl
theorem A_size_eq2 (b : B) : (A.other b).size = b.size + 1 := rfl
theorem A_size_eq3 : A.empty.size = 0  := rfl
theorem B_size_eq1 (b : B) : (B.self b).size = b.size + 1 := rfl
theorem B_size_eq2 (a : A) : (B.other a).size = a.size + 1 := rfl
theorem B_size_eq3 : B.empty.size = 0  := rfl

end MutualIndNonMutualFun
