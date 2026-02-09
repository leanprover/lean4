/-!
# Test that `exact?` and `rw?` do not suggest deprecated lemmas
-/

-- Create a deprecated lemma and its non-deprecated replacement
@[deprecated "use myLemma2" (since := "2025-01-01")]
theorem myLemma1 : True := trivial

theorem myLemma2 : True := trivial

-- Test that exact? suggests myLemma2, not the deprecated myLemma1
/--
info: Try this:
  [apply] exact myLemma2
-/
#guard_msgs in
example : True := by exact?

-- Create a unique type so our lemmas are the only matches
structure MyType where
  val : Nat

def myFn (x : MyType) : MyType := x

-- Create deprecated and non-deprecated rewrite lemmas with unique signature
@[deprecated "use myRwLemma2" (since := "2025-01-01")]
theorem myRwLemma1 (x : MyType) : myFn (myFn x) = myFn x := rfl

theorem myRwLemma2 (x : MyType) : myFn (myFn x) = myFn x := rfl

-- Test that rw? suggests myRwLemma2, not the deprecated myRwLemma1
/--
info: Try this:
  [apply] rw [myRwLemma2]
  -- no goals
-/
#guard_msgs in
example (x : MyType) : myFn (myFn x) = myFn x := by rw?
