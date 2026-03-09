-- Artificial example for exposing a regression introduced while working on PR #5376
-- fix: modify projection instance binder info

class Foo (α : Type) [Add α] where
   bla : [Mul α] → BEq α

attribute [instance] Foo.bla

inductive Boo where
  | unit

instance : Add Boo where
  add _ _ := .unit

instance : Mul Boo where
  mul _ _ := .unit

def f [Foo Boo] (a b : Boo) : Bool :=
  a == b
