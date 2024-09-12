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

/-- info: a1 =?= a2 := true -/
#guard_msgs in
#eval checkDefEq `a1 `a2

/-- info: a1 =?= a3 := false -/
#guard_msgs in
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

/-- info: c1 =?= c2 := true -/
#guard_msgs in
#eval checkDefEq `c1 `c2

/-- info: c1 =?= c3 := false -/
#guard_msgs in
#eval checkDefEq `c1 `c3

/-- info: c5 =?= Nat.zero := true -/
#guard_msgs in
#eval checkDefEq `c5 `Nat.zero

/-- info: Nat.zero =?= c5 := true -/
#guard_msgs in
#eval checkDefEq `Nat.zero `c5

/-- info: c4 =?= Bool.true := false -/
#guard_msgs in
#eval checkDefEq `c4 `Bool.true
