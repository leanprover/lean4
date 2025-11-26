/-!
Tests that definitions by well-founded recursion are irreducible.
-/

set_option pp.mvars false

def foo : Nat → Nat
  | 0 => 0
  | n+1 => foo n
termination_by n => n

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 = 0
-/
#guard_msgs in
example : foo 0 = 0 := rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo (n + 1) = foo n
-/
#guard_msgs in
example : foo (n+1) = foo n := rfl

-- also for closed terms
/--
error: Tactic `rfl` failed: The left-hand side
  foo 0
is not definitionally equal to the right-hand side
  0

⊢ foo 0 = 0
-/
#guard_msgs in
example : foo 0 = 0 := by rfl

-- It only works on closed terms:
/--
error: Tactic `rfl` failed: The left-hand side
  foo (n + 1)
is not definitionally equal to the right-hand side
  foo n

n : Nat
⊢ foo (n + 1) = foo n
-/
#guard_msgs in
example : foo (n+1) = foo n := by rfl

section Unsealed

unseal foo

-- unsealing works, but does not have the desired effect

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 = 0
-/
#guard_msgs in
example : foo 0 = 0 := rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo (n + 1) = foo n
-/
#guard_msgs in
example : foo (n+1) = foo n := rfl

end Unsealed

--should be sealed again here

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 = 0
-/
#guard_msgs in
example : foo 0 = 0 := rfl

def bar : Nat → Nat
  | 0 => 0
  | n+1 => bar n
termination_by n => n

-- Once unsealed, the full internals are visible. This allows one to prove, for example
-- an equality like the following

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo = bar
-/
#guard_msgs in
example : foo = bar := rfl

unseal foo bar in
example : foo = bar := rfl
