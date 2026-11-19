module

set_option backward.do.legacy false

set_option linter.unusedVariables.funArgs false in
def Quoted (x : Nat) := Nat

def withStuff (x : Nat) (f : IO (Quoted x)) : IO (Quoted x) := f

def myFunc : IO Nat := do
  let val : Nat ← pure 3
  withStuff val do
    return (3 : Nat)
