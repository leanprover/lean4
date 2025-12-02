import Lean
open Lean

structure X
structure Y

def convert (_ : X) : Y := ⟨⟩

@[deprecated convert (since := "")]
instance mycoe : Coe X Y where coe _ := ⟨⟩

def f : Option String := "hi"

def g : Array Nat := #[1, 2, 3][*...*]

def h (foo : X) : Y := foo
