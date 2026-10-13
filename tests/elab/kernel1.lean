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
