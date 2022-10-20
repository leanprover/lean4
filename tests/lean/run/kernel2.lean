import Lean

open Lean

def checkDefEq (a b : Name) : CoreM Unit := do
  let env ← getEnv
  let a := mkConst a
  let b := mkConst b
  let r ← ofExceptKernelException (Kernel.isDefEq env {} a b)
  IO.println (toString a ++ " =?= " ++ toString b ++ " := " ++ toString r)

def whnf (a : Name) : CoreM Unit := do
  let env ← getEnv
  let a := mkConst a
  let r ← ofExceptKernelException (Kernel.whnf env {} a)
  IO.println (toString a ++ " ==> " ++ toString r)

partial def fact : Nat → Nat
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

def c4 := decide (100000000 < 20000000000)

#eval whnf `c4
#eval checkDefEq `c4 `Bool.true

def c5 := "h".length
def c6 := 1
set_option pp.all true

#eval whnf `c5
#eval checkDefEq `c5 `c6

def c7 := decide ("hello" = "world")
#eval whnf `c7

def c8 := "hello".length

#eval whnf `c8

def c9  : String := "hello" ++ "world"
def c10 : String := "helloworld"

#eval checkDefEq `c9 `c10

def c11 : Bool := decide ('a' = 'b')

#eval whnf `c11

def c12 : Nat := 'a'.toNat

#eval whnf `c12
