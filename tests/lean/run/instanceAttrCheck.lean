/-!
# Check that the `instance` attribute is on an instance
-/

inductive Foo where | mk

/--
error: type class instance expected
  Foo
-/
#guard_msgs in
instance : Foo := ⟨⟩

/--
error: type class instance expected
  Foo
-/
#guard_msgs in
@[instance] def fn : Foo := ⟨⟩


-- Checks that the attribute check happens for the right function,
-- even with mutually well-founded recursive functions

class C (n m : Nat) : Type where

mutual
@[instance]
def foo : (n m : Nat) → C n m
  | 0, _m => C.mk
  | n+1, m => let _ := bar n m; C.mk
def bar : (n m : Nat) → C n m
  | 0, _m => C.mk
  | n+1, m => let _ := foo n m; C.mk
end

/-- info: foo 23 23 -/
#guard_msgs in
#synth C 23 23
