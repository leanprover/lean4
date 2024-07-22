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


/-!
Check that intermediate definitions (here produced by WF recursion processing)
do not also get the `@[instance]` attribute.
-/

class C (n : Nat) : Type where

mutual
@[instance]
def foo : (n : Nat) → C n
  | 0 => C.mk
  | n+1 => let _ := bar n; C.mk
termination_by n => n
def bar : (n : Nat) → C n
  | 0 => C.mk
  | n+1 => let _ := foo n; C.mk
termination_by n => n
end

/-- info: foo 23 -/
#guard_msgs in
#synth C 23
