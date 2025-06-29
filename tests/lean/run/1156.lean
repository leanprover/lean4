inductive Foo : Nat -> Type  where
| mk (a b : Nat) : Foo a -> Foo b

/-- info: Foo.mk : (a b : Nat) → Foo a → Foo b -/
#guard_msgs in
#check @Foo.mk
example : (a b : Nat) → Foo a → Foo b := @Foo.mk

/--
info: inductive Foo : Nat → Type
number of parameters: 0
constructors:
Foo.mk : (a b : Nat) → Foo a → Foo b
-/
#guard_msgs in
#print Foo

namespace Ex2

def natToType : Nat → Type
| 0 => Unit
| _ => Bool

inductive Foo : Nat → Char → Prop
| mk (n : Nat) (elem : natToType n) (c : Char) : Foo n c

/--
info: inductive Ex2.Foo : Nat → Char → Prop
number of parameters: 1
constructors:
Ex2.Foo.mk : ∀ (n : Nat) (elem : natToType n) (c : Char), Foo n c
-/
#guard_msgs in
#print Foo

end Ex2
