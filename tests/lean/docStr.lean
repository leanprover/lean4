import Lean

/-- Foo structure is just a test -/
structure Foo where
  /-- main name -/ name : String := "hello"
  /-- documentation for the second field -/ val : Nat := 0

/-- documenting test axiom -/
axiom myAxiom : Nat

structure Boo (α : Type) where
  /-- Boo constructor has a custom name -/
  makeBoo ::
    /-- Boo.x docString -/ x : Nat
    y : Bool

/-- inductive datatype Tree documentation -/
inductive Tree (α : Type) where
  | /-- Tree.node documentation -/ node : List (Tree α) → Tree α
  | /-- Tree.leaf stores the values -/ leaf : α → Tree α

namespace Bla

/-- documenting definition in namespace -/
def test (x : Nat) : Nat :=
  aux x + 1
where
  /-- We can document 'where' functions too -/
  aux x := x + 2

end Bla

def f (x : Nat) : IO Nat := do
  let rec /-- let rec documentation at f -/ foo
    | 0   => 1
    | x+1 => foo x + 2
  return foo x

def g (x : Nat) : Nat :=
  let rec /-- let rec documentation at g -/ foo
    | 0   => 1
    | x+1 => foo x + 2
  foo x

open Lean

def printDocString (declName : Name) : MetaM Unit := do
  match (← getDocString? declName) with
  | some docStr => IO.println (repr docStr)
  | none => IO.println s!"doc string for '{declName}' is not available"

def printDocStrings : MetaM Unit := do
  printDocString `Foo
  printDocString `Foo.name
  printDocString `Foo.val
  printDocString `myAxiom
  printDocString `Boo
  printDocString `Boo.makeBoo
  printDocString `Boo.x
  printDocString `Boo.y
  printDocString `Tree
  printDocString `Tree.node
  printDocString `Tree.leaf
  printDocString `Bla.test
  printDocString `Bla.test.aux
  printDocString `f
  printDocString `f.foo
  printDocString `g
  printDocString `g.foo
  printDocString `optParam
  printDocString `namedPattern
  printDocString `Lean.Meta.forallTelescopeReducing

#eval printDocStrings
