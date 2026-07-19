import Lean

macro "gen_term" n:num : term => do
  let mut stx ← `(True)
  for _ in 0...n.getNat do
    stx := ← `(let z : Nat := x + y; let y := y + 1; have : y >= 0 := Nat.zero_le y; forall x : Nat, $stx)
  `(let z : Nat := 0 ; forall x : Nat, forall y : Nat, $stx)

open Lean Meta Sym Elab Tactic

def test (mvarId : MVarId) : MetaM MVarId := do
  SymM.run do
    let .goal _ mvarId ← intros mvarId | failure
    return mvarId

/--
trace: z✝² : Nat := 0
x✝² y✝² : Nat
z✝¹ : Nat := x✝² + y✝²
y✝¹ : Nat := y✝² + 1
this✝¹ : y✝¹ ≥ 0 := Nat.zero_le y✝¹
x✝¹ : Nat
z✝ : Nat := x✝¹ + y✝¹
y✝ : Nat := y✝¹ + 1
this✝ : y✝ ≥ 0 := Nat.zero_le y✝
x✝ : Nat
⊢ True
-/
#guard_msgs in
example : gen_term 2 := by
  run_tac liftMetaTactic1 fun mvarId => test mvarId
  trace_state
  constructor

example : gen_term 70 := by
  run_tac liftMetaTactic1 fun mvarId => test mvarId
  constructor

def testUnhygienic  (mvarId : MVarId) : MetaM MVarId := do
  SymM.run do
    let .goal _ mvarId ← intros mvarId (hygienic := false) | failure
    return mvarId

/--
trace: z : Nat := 0
x y : Nat
z_1 : Nat := x + y
y_1 : Nat := y + 1
this : y_1 ≥ 0 := Nat.zero_le y_1
x_1 : Nat
⊢ True
-/
#guard_msgs in
example : gen_term 1 := by
  run_tac liftMetaTactic1 fun mvarId => testUnhygienic mvarId
  trace_state
  constructor
