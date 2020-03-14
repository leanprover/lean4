import Init.Lean

open Lean

def checkDefEq (a b : Name) : MetaIO Unit := do
env ← MetaIO.getEnv;
let a := mkConst a;
let b := mkConst b;
let r := Kernel.isDefEq env {} a b;
IO.println (toString a ++ " =?= " ++ toString b ++ " := " ++ toString r)


def a1 := 100 + 100
def a2 := 200
def a3 := 20

#eval checkDefEq `a1 `a2
#eval checkDefEq `a1 `a3
