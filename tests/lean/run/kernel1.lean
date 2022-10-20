import Lean

open Lean

def checkDefEq (a b : Name) : CoreM Unit := do
  let env ← getEnv
  let a := mkConst a
  let b := mkConst b
  let r ← ofExceptKernelException (Kernel.isDefEq env {} a b)
  IO.println (toString a ++ " =?= " ++ toString b ++ " := " ++ toString r)


def a1 := 100 + 100
def a2 := 200
def a3 := 20

#eval checkDefEq `a1 `a2
#eval checkDefEq `a1 `a3

def v1 := 100000000000 + 100000000000
def v2 := 200000000000
def v3 := 200000000001
def v4 : Bool := 20000000000 > 200000000001
def v5 := 100000000000 - 100000000000

def c1 := reduceNat v1
def c2 := reduceNat v2
def c3 := reduceNat v3
def c4 := reduceBool v4
def c5 := reduceNat v5

#eval checkDefEq `c1 `c2
#eval checkDefEq `c1 `c3
#eval checkDefEq `c5 `Nat.zero
#eval checkDefEq `Nat.zero `c5

#eval checkDefEq `c4 `Bool.true
