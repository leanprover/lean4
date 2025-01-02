import Lean.Meta.Tactic.Grind

open Lean Meta Grind in
def fallback : Fallback := do
  let trueExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqTrue e.self)).toList.map (·.self)
  let falseExprs := (← filterENodes fun e => return e.self.isFVar && (← isEqFalse e.self)).toList.map (·.self)
  logInfo m!"true:  {trueExprs}"
  logInfo m!"false: {falseExprs}"
  forEachEqc fun n => do
    unless (← isProp n.self) || (← isType n.self) || n.size == 1 do
      let eqc ← getEqc n.self
      logInfo eqc
  (← get).mvarId.admit

set_option grind.debug true
set_option grind.debug.proofs true

/--
info: true:  [q, w]
---
info: false: [p, r]
-/
#guard_msgs (info) in
example : (p ∨ (q ∧ ¬r ∧ w)) → ¬p → False := by
  grind on_failure fallback


/--
info: true:  [r]
---
info: false: [p, q]
-/
#guard_msgs (info) in
example : (p ∨ q ∨ r) → (p ∨ ¬q) → ¬p → False := by
  grind on_failure fallback


/--
info: true:  [r]
---
info: false: [p₁, q]
-/
#guard_msgs (info) in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → (p₁ ∨ ¬q) → p₁ = False → False := by
  grind on_failure fallback

/--
info: true:  [r]
---
info: false: [p₂, q]
-/
#guard_msgs (info) in
example : ((p₁ ∧ p₂) ∨ q ∨ r) → ((p₂ ∧ p₁) ∨ ¬q) → p₂ = False → False := by
  grind on_failure fallback

/--
info: true:  [q, r]
---
info: false: [p]
-/
#guard_msgs (info) in
example (p q r : Prop) : p ∨ (q ↔ r) → p = False → q → False := by
  grind on_failure fallback

/--
info: true:  [r]
---
info: false: [p, s]
-/
#guard_msgs (info) in
example (p q r : Prop) : p ∨ ¬(s ∨ (p ↔ r)) → p = False → False := by
  grind on_failure fallback

/--
info: true:  [p]
---
info: false: []
---
info: [a, b]
-/
#guard_msgs (info) in
example (p : Prop) (a : Vector Nat 5) (b : Vector Nat 6) : (p → HEq a b) → p → False := by
  grind on_failure fallback

/--
info: true:  [p, q]
---
info: false: [r]
-/
#guard_msgs (info) in
example (p q r : Prop) : p ∨ (q ↔ r) → q → ¬r → False := by
  grind on_failure fallback

/--
info: hello world
---
info: true:  [p, q]
---
info: false: [r]
-/
#guard_msgs (info) in
example (p q r : Prop) : p ∨ (q ↔ r) → ¬r → q → False := by
  grind on_failure do
    Lean.logInfo "hello world"
    fallback
