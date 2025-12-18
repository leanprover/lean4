import Lean

-- set_option trace.Meta.FunInd true

axiom testSorry : α

def test (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match x == 3 with
    | false => test l
    | true => test l

/--
info: test.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 : ∀ (x : Nat) (l : List Nat), (x == 3) = false → motive l (test l) → motive (x :: l) (test l))
  (case3 : ∀ (x : Nat) (l : List Nat), (x == 3) = true → motive l (test l) → motive (x :: l) (test l)) (l : List Nat) :
  motive l (test l)
-/
#guard_msgs in
#check test.induct_unfolding

opaque someFunction (x : Nat) (h : (x == 3) = false) : Nat
opaque someOtherFunction (x : Nat) (h : (x == 3) = true) : Nat

def deptest (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | x :: l =>
    match h : x == 3 with
    | false => deptest l + someFunction x h
    | true => deptest l + someOtherFunction x h

/--
info: deptest.induct_unfolding (motive : List Nat → Nat → Prop) (case1 : motive [] 0)
  (case2 :
    ∀ (x : Nat) (l : List Nat) (h : (x == 3) = false),
      motive l (deptest l) → motive (x :: l) (deptest l + someFunction x h))
  (case3 :
    ∀ (x : Nat) (l : List Nat) (h : (x == 3) = true),
      motive l (deptest l) → motive (x :: l) (deptest l + someOtherFunction x h))
  (l : List Nat) : motive l (deptest l)
-/
#guard_msgs in
#check deptest.induct_unfolding

-- This one doesn't work, the result type varies in the branches
-- But we fail gracefully
def depTestOddType (l : List Nat) :
    match l with
    | [] => Unit
    | x :: _ =>
      if x == 3 then
        Unit
      else
        Nat
  :=
  match l with
  | [] => ()
  | x :: _ =>
    (match h : x == 3 with
    | false => someFunction x h
    | true => () : if x == 3 then Unit else Nat)

/--
info: depTestOddType.fun_cases_unfolding
  (motive :
    (l : List Nat) →
      (match l with
        | [] => Unit
        | x :: tail => if (x == 3) = true then Unit else Nat) →
        Prop)
  (case1 : motive [] ())
  (case2 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = false →
        motive (x :: l)
          (match h : x == 3 with
          | false => someFunction x h
          | true => ()))
  (case3 :
    ∀ (x : Nat) (l : List Nat),
      (x == 3) = true →
        motive (x :: l)
          (match h : x == 3 with
          | false => someFunction x h
          | true => ()))
  (l : List Nat) : motive l (depTestOddType l)
-/
#guard_msgs in
#check depTestOddType.fun_cases_unfolding

-- set_option trace.Meta.FunInd true in
set_option linter.unusedVariables false in
def testMe (n : Nat) : Bool :=
  match _ : n - 2 with
  | 0 => true
  | m => false

/--
info: testMe.fun_cases_unfolding (n : Nat) (motive : Bool → Prop) (case1 : n - 2 = 0 → motive true)
  (case2 : (n - 2 = 0 → False) → motive false) : motive (testMe n)
-/
#guard_msgs in
#check testMe.fun_cases_unfolding
