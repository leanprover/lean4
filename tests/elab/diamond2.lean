structure Bar (α : Type) where
  a : α
  x : Nat → α

structure Baz (α : Type) where
  a : α → α
  β : Type
  b : α → β

set_option structureDiamondWarning false

structure Foo1 (α : Type) extends Bar (α → α), Baz α

#check Foo1.mk

def f1 (x : Nat) : Foo1 Nat :=
  { β := _
    a := id
    x := (· + ·)
    b := fun _ => "" }

structure Boo1 (α : Type) extends Baz α where
  x1 : α

structure Boo2 (α : Type) extends Boo1 α where
  x2 : α

structure Foo2 (α : Type) extends Bar (α → α), Boo2 α

#check Foo2.mk

def f2 (v : Nat) : Foo2 Nat :=
  { β  := _
    a  := id
    x  := (· + ·)
    b  := fun _ => ""
    x1 := 1
    x2 := v }

theorem ex2 (v : Nat) : (f2 v |>.x2) = v :=
  rfl

#print Foo2.toBar
#print Foo2.toBoo2
