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

def check (a : Name) : CoreM Unit := do
  let env ← getEnv
  let a := mkConst a
  let r ← ofExceptKernelException (Kernel.check env {} a)
  IO.println (toString a ++ " ==> " ++ toString r)

partial def fact : Nat → Nat
| 0     => 1
| (n+1) => (n+1)*fact n

def c1 := 30000000000 + 10000000000
def c2 := 40000000000
def c3 := fact 10
def v1  := 3628800
def v2  := 3628801

/-- info: c3 ==> fact (OfNat.ofNat.{0} Nat 10 (instOfNatNat 10)) -/
#guard_msgs in
#eval whnf `c3

/-- info: c3 =?= v1 := false -/
#guard_msgs in
#eval checkDefEq `c3 `v1

/-- info: c3 =?= v2 := false -/
#guard_msgs in
#eval checkDefEq `c3 `v2

/-- info: c1 =?= c2 := true -/
#guard_msgs in
#eval checkDefEq `c1 `c2

def c4 := decide (100000000 < 20000000000)

/-- info: c4 ==> Bool.true -/
#guard_msgs in
#eval whnf `c4

/-- info: c4 =?= Bool.true := true -/
#guard_msgs in
#eval checkDefEq `c4 `Bool.true

def c5 := "h".length
def c6 := 1
set_option pp.all true

/-- info: c5 ==> 1 -/
#guard_msgs in
#eval whnf `c5

/-- info: c5 =?= c6 := true -/
#guard_msgs in
#eval checkDefEq `c5 `c6

def c7 := decide ("hello" = "world")

/-- info: c7 ==> Bool.false -/
#guard_msgs in
#eval whnf `c7

def c8 := "hello".length

/-- info: c8 ==> 5 -/
#guard_msgs in
#eval whnf `c8

def c9  : String := "hello" ++ "world"
def c10 : String := "helloworld"

/-- info: c9 =?= c10 := true -/
#guard_msgs in
#eval checkDefEq `c9 `c10

def c11 : Bool := decide ('a' = 'b')

/-- info: c11 ==> Bool.false -/
#guard_msgs in
#eval whnf `c11

def c12 : Nat := 'a'.toNat

/-- info: c12 ==> 97 -/
#guard_msgs in
#eval whnf `c12

/-- info: c11 ==> Bool -/
#guard_msgs in
#eval check `c11
