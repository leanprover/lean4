import Std.Control.Nondet

open Std

namespace ex1
-- The state is not backtrackable
abbrev M := NondetT $ StateT Nat $ IO

def checkVal (x : Nat) : M Nat := do
  IO.println s!"x: {x}"
  guard (x % 2 == 0)
  pure x

def f : M Nat := do
  let x ← NondetT.choose [1, 2, 3, 4, 5, 6, 7, 8]
  checkVal x

def h : M Nat := do
  let a ← f
  modify (· + 1)
  guard (a % 3 == 0)
  pure (a+1)

def g : IO Unit :=  do
  let (some (x, _), s) ← h.run.run 0 | throw $ IO.userError "failed"
  IO.println s!"x: {x}, s: {s}"

#eval g
end ex1

namespace ex2
-- The state is backtrackable
abbrev M := StateT Nat $ NondetT $ IO

def checkVal (x : Nat) : M Nat := do
  IO.println s!"x: {x}"
  guard (x % 2 == 0)
  pure x

def f : M Nat := do
  let x ← NondetT.choose [1, 2, 3, 4, 5, 6, 7, 8]
  checkVal x

def h : M Nat := do
  let a ← f
  modify (· + 1)
  guard (a % 3 == 0)
  pure (a+1)

def g : IO Unit :=  do
  let some ((x, s), _) ← (h.run 0).run | throw $ IO.userError "failed"
  IO.println s!"x: {x}, s: {s}"

#eval g
end ex2

namespace ex3
abbrev M := NondetT IO

def a : M Unit := IO.println "a"
def b : M Unit := IO.println "b"
def c : M Unit := IO.println "c"

def t1 : M Unit :=
  ((a <|> a) *> b) *> c

def t2 : M Unit :=
  (a <|> a) *> (b *> c)

#eval t1.run'
#eval t2.run'

end ex3
