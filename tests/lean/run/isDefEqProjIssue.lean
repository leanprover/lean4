import Lean
open Lean

-- We need a structure as this is related to isDefEq problems of the form `e1.proj =?= e2.proj`.
structure Test where
  x : Nat

-- We need a data structure with functions that are not meant for reduction purposes.
abbrev Cache := HashMap Nat Test

def Cache.insert (cache : Cache) (key : Nat) (val : Test) : Cache :=
  HashMap.insert cache key val

def Cache.find? (cache : Cache) (key : Nat) : Option Test :=
  HashMap.find? cache key

-- This function just contains a call to a function that we definitely do not want to reduce.
-- To illustrate that the problem is actually noticeable there are multiple implementations provided.
-- Each of these implementations does additional modifications on the cache before looking things up,
-- as one might expect in irl functions.
-- Each version has a lot of additional complexity from the type checkers POV.
def barImpl1 (cache : Cache) (key : Nat) : Test :=
  match cache.find? key with
  | some val => val
  | none => ⟨0⟩

def barImpl2 (cache : Cache) (key : Nat) : Test :=
  match (cache.insert key ⟨0⟩).find? key with
  | some val => val
  | none => ⟨0⟩

def barImpl3 (cache : Cache) (key : Nat) : Test :=
  match ((cache.insert key ⟨0⟩).insert 0 ⟨0⟩).find? key with
  | some val => val
  | none => ⟨0⟩

def barImpl4 (cache : Cache) (key : Nat) : Test :=
  match (((cache.insert key ⟨0⟩).insert 0 ⟨0⟩).insert key ⟨key⟩).find? key with
  | some val => val
  | none => ⟨0⟩

def bar := barImpl4

set_option maxHeartbeats 400 in
def test (c1 : Cache) (key : Nat) : Nat :=
  go c1 key
where
  go (c1 : Cache) (key : Nat) : Nat :=
    let val : Test := bar c1 key
    have : val.x = (bar c1 key).x := rfl
    val.x

/--
error: (deterministic) timeout at `whnf`, maximum number of heartbeats (400) has been reached
Use `set_option maxHeartbeats <num>` to set the limit.

Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.lazyWhnfCore false in
set_option maxHeartbeats 400 in
def test' (c1 : Cache) (key : Nat) : Nat :=
  go c1 key
where
  go (c1 : Cache) (key : Nat) : Nat :=
    let val : Test := bar c1 key
    have : val.x = (bar c1 key).x := rfl
    val.x

def ack : Nat → Nat → Nat
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)

class Foo where
  x : Nat
  y : Nat

instance f (x : Nat) : Foo :=
  { x, y := ack 10 10 }

instance g (x : Nat) : Foo :=
  { x, y := ack 10 11 }

open Lean Meta
set_option maxHeartbeats 400 in
run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let lhs := Expr.proj ``Foo 0 <| mkApp (mkConst ``f) x
    let rhs := Expr.proj ``Foo 0 <| mkApp (mkConst ``g) x
    assert! (← isDefEq lhs rhs)

run_meta do
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let lhs := Expr.proj ``Foo 0 <| mkApp (mkConst ``f) x
    let rhs := Expr.proj ``Foo 0 <| mkApp (mkConst ``g) x
    match Kernel.isDefEq (← getEnv) {} lhs rhs with
    | .ok b => assert! b
    | .error _ => throwError "failed"

example : (f x).1 = (g x).1 :=
  rfl
