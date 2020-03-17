import Init.Lean
open Lean

def checkDefEq (a b : Name) : MetaIO Unit := do
env ← MetaIO.getEnv;
let a := mkConst a;
let b := mkConst b;
let r := Kernel.isDefEq env {} a b;
IO.println (toString a ++ " =?= " ++ toString b ++ " := " ++ toString r)

def whnf (a : Name) : MetaIO Unit := do
env ← MetaIO.getEnv;
let a := mkConst a;
let r := Kernel.whnf env {} a;
IO.println (toString a ++ " ==> " ++ toString r)

def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

def c1 := 30000000000 + 10000000000
def c2 := 40000000000
def c3 := fact 10
def v1  := 3628800
def v2  := 3628801
#eval whnf `c3
#eval checkDefEq `c3 `v1
#eval checkDefEq `c3 `v2
#eval checkDefEq `c1 `c2

set_option pp.all true

def c4 := decide (100000000 < 20000000000)

#eval whnf `c4
#eval checkDefEq `c4 `Bool.true
