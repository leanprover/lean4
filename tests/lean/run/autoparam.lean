/-!
# Testing the autoparam feature
-/

def f (x y : Nat) (h : x = y := by assumption) : Nat :=
x + x

def g (x y z : Nat) (h : x = y) : Nat :=
f x y

def f2 (x y : Nat) (h : x = y := by exact rfl) : Nat :=
x + x

def f3 (x y : Nat) (h : x = y := by exact Eq.refl x) : Nat :=
x + x

#check fun x => f2 x x
#check fun x => f3 x x

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: tactic 'assumption' failed
⊢ 1 = 2
-/
#guard_msgs in example := f 1 2

/-!
From #2950, field autoparam should mention which field failed.
-/

structure Foo where
  val : String
  len : Nat := val.length
  inv : val.length = len := by next => decide

/--
error: could not synthesize default value for field 'inv' of 'Foo' using tactics
---
error: tactic 'decide' proved that the proposition
  "abc".length = 5
is false
-/
#guard_msgs in
def test2 : Foo := {
  val := "abc"
  len := 5
}
