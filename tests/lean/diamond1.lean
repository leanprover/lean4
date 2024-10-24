structure Bar (α : Type) where
  a : α
  b : Nat → α

structure Baz (α : Type) where
  a : α → α
  c : Bool → α
  d : Nat

set_option structure.diamondWarning false in
structure Foo (α : Type) extends Bar α, Baz α -- Error: parent field type mismatch

set_option structure.diamondWarning false in
structure Foo (α : Type) extends Bar (α → α), Baz α

#print Foo

def f (x : Nat) : Foo Nat :=
  { a := fun y => x + y
    b := (· + ·)
    c := fun _ => x
    d := x }

#print f

set_option structure.diamondWarning true in
structure Foo' (α : Type) extends Bar (α → α), Baz α -- Warning: parent field duplication
