open Lean

def foo : Name := `foo

def isFoo : Name → Bool
  | ``foo => true
  | _     => false

theorem ex1 : isFoo `foo = true  := rfl
theorem ex2 : isFoo `bla = false := rfl

def Bla.boo : Name := `boo

open Bla

def isBoo : Name → Bool
  | ``boo => true
  | _     => false

theorem ex3 : isBoo `Bla.boo = true := rfl
theorem ex4 : isBoo ``boo = true := rfl
theorem ex5 : ``boo = `Bla.boo := rfl
