inductive Foo : Nat -> Type  where
| mk (a b : Nat) : Foo a -> Foo b

#check @Foo.mk
example : (a b : Nat) → Foo a → Foo b := @Foo.mk

#print Foo

namespace Ex2

def natToType : Nat → Type
| 0 => Unit
| _ => Bool

inductive Foo : Nat → Char → Prop
| mk (n : Nat) (elem : natToType n) (c : Char) : Foo n c

#print Foo

end Ex2
