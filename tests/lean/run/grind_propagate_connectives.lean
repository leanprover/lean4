import Lean.Meta.Tactic.Grind

set_option trace.Meta.debug true

open Lean Meta Grind in
def fallback : Fallback := do
  let trueExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqTrue e.self)).toList.map (·.self)
  let falseExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqFalse e.self)).toList.map (·.self)
  trace[Meta.debug] "true:  {trueExprs}"
  trace[Meta.debug] "false: {falseExprs}"
  forEachEqcRoot fun n => do
    unless (← isProp n.self) || (← isType n.self) || n.size == 1 do
      let eqc ← getEqc n.self
      trace[Meta.debug] eqc
  (← get).mvarId.admit

set_option grind.debug true
set_option grind.debug.proofs true

/--
trace: [Meta.debug] true:  [q, w]
[Meta.debug] false: [p, r]
-/
#guard_msgs (trace) in
example : (p ∨ (q ∧ ¬r ∧ w)) → ¬p → False := by
  grind on_failure fallback


/--
trace: [Meta.debug] true:  [r]
[Meta.debug] false: [p, q]
-/
#guard_msgs (trace) in
example : (p ∨ q ∨ r) → (p ∨ ¬q) → ¬p → False := by
  grind on_failure fallback


/--
trace: [Meta.debug] true:  [r]
[Meta.debug] false: [p₁, q]
-/
#guard_msgs (trace) in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → (p₁ ∨ ¬q) → p₁ = False → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] true:  [r]
[Meta.debug] false: [p₂, q]
-/
#guard_msgs (trace) in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → ((p₂ ∧ p₁) ∨ ¬q) → p₂ = False → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] true:  [q, r]
[Meta.debug] false: [p]
-/
#guard_msgs (trace) in
example (p q r : Prop) : p ∨ (q ↔ r) → p = False → q → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] true:  [r]
[Meta.debug] false: [p, s]
-/
#guard_msgs (trace) in
example (p q r : Prop) : p ∨ ¬(s ∨ (p ↔ r)) → p = False → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] true:  [p]
[Meta.debug] false: []
[Meta.debug] [b, a]
-/
#guard_msgs (trace) in
example (p : Prop) (a : Vector Nat 5) (b : Vector Nat 6) : (p → a ≍ b) → p → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] true:  [p, q]
[Meta.debug] false: [r]
-/
#guard_msgs (trace) in
example (p q r : Prop) : p ∨ (q ↔ r) → q → ¬r → False := by
  grind on_failure fallback

/--
trace: [Meta.debug] hello world
[Meta.debug] true:  [p, q]
[Meta.debug] false: [r]
-/
#guard_msgs (trace) in
example (p q r : Prop) : p ∨ (q ↔ r) → ¬r → q → False := by
  grind on_failure do
    trace[Meta.debug] "hello world"
    fallback

example (a b : Nat) : (a = b) = (b = a) := by
  grind
