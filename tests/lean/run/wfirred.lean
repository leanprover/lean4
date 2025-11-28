/-!
Tests that definitions by well-founded recursion (not on Nat) are irreducible.
-/

set_option pp.mvars false

def foo : Nat → Nat → Nat
  | 0,  m => m
  | n+1, m => foo n (m + n)
termination_by n m => (n, m)

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 m = m
-/
#guard_msgs in
example : foo 0 m = m := rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo (n + 1) m = foo n (m + n)
-/
#guard_msgs in
example : foo (n+1) m = foo n (m + n) := rfl

-- also for closed terms
/--
error: Tactic `rfl` failed: The left-hand side
  foo 0 0
is not definitionally equal to the right-hand side
  0

⊢ foo 0 0 = 0
-/
#guard_msgs in
example : foo 0 0 = 0 := by rfl

section Unsealed

unseal foo

-- unsealing works, but does not have the desired effect

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 0 = 0
-/
#guard_msgs in
example : foo 0 0 = 0 := rfl

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo (n + 1) m = foo n (n + m)
-/
#guard_msgs in
example : foo (n+1) m = foo n (n +m ):= rfl

end Unsealed

--should be sealed again here

/--
error: Type mismatch
  rfl
has type
  ?_ = ?_
but is expected to have type
  foo 0 m = m
-/
#guard_msgs in
example : foo 0 m = m := rfl

def bar : Nat → Nat → Nat
  | 0, m => m
  | n+1, m => bar n (m + n)
termination_by n m => (n, m)

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
