import Lean

open Lean Meta Grind Elab Tactic in
elab "cases' " e:term : tactic => withMainContext do
  let e ← elabTerm e none
  setGoals (← Grind.cases (← getMainGoal) e)

inductive Vec (α : Type u) : Nat → Type u
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n+1)

def f (v : Vec α n) : Bool :=
  match v with
  | .nil => true
  | .cons .. => false

/--
info: n : Nat
v : Vec Nat n
h : f v ≠ false
⊢ n + 1 = 0 → HEq (Vec.cons 10 v) Vec.nil → False
---
info: n : Nat
v : Vec Nat n
h : f v ≠ false
⊢ ∀ {n_1 : Nat} (a : Nat) (a_1 : Vec Nat n_1), n + 1 = n_1 + 1 → HEq (Vec.cons 10 v) (Vec.cons a a_1) → False
-/
#guard_msgs (info) in
example (v : Vec Nat n) (h : f v ≠ false) : False := by
  cases' (Vec.cons 10 v)
  next => trace_state; sorry
  next => trace_state; sorry

/--
info: ⊢ False → False
---
info: ⊢ True → False
-/
#guard_msgs (info) in
example : False := by
  cases' (Or.inr (a := False) True.intro)
  next => trace_state; sorry
  next => trace_state; sorry
