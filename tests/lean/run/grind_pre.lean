import Lean

open Lean Meta Elab Tactic Grind in
elab "grind_pre" : tactic => do
  let declName := (← Term.getDeclName?).getD `_main
  liftMetaTactic fun mvarId => do
    let result ← Meta.Grind.main mvarId declName
    return result.goals.map (·.mvarId) |>.toList

abbrev f (a : α) := a

/--
warning: declaration uses 'sorry'
---
info: a b c : Bool
p q : Prop
left✝ : a = true
right✝ : b = true ∨ c = true
left : p
right : q
x✝ : b = false ∨ a = false
⊢ False
-/
#guard_msgs in
theorem ex (h : (f a && (b || f (f c))) = true) (h' : p ∧ q) : b && a := by
  grind_pre
  trace_state
  sorry

def g (i : Nat) (j : Nat) (_ : i > j := by omega) := i + j

example (i j : Nat) (h : i + 1 > j + 1) : g (i+1) j = f ((fun x => x) i) + f j + 1 := by
  grind_pre
  guard_hyp h : j + 1 ≤ i
  next hn =>
  guard_hyp hn : ¬g (i + 1) j _ = i + j + 1
  simp_arith [g] at hn
