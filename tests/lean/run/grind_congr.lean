module
meta import Lean
#exit

def f (a : Nat) := a + a + a
def g (a : Nat) := a + a

-- Prints the equivalence class containing a `f` application
open Lean Meta Grind in
meta def fallback : Fallback := do
  let #[n, _] ← filterENodes fun e => return e.self.isApp && e.self.isAppOf ``f | unreachable!
  let eqc ← getEqc n.self (sort := true)
  trace[Meta.debug] eqc
  (← get).mvarId.admit

set_option trace.Meta.debug true
set_option grind.debug true
set_option grind.debug.proofs true

/-- trace: [Meta.debug] [c, d, f a, f b] -/
#guard_msgs (trace) in
example (a b c d : Nat) : a = b → f a = c → f b = d → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] [c, d, f a, f b] -/
#guard_msgs (trace) in
example (a b c d : Nat) : f a = c → f b = d → a = b → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] [c, d, f (g a), f (g b)] -/
#guard_msgs (trace) in
example (a b c d e : Nat) : f (g a) = c → f (g b) = d → a = e → b = e → False := by
  grind on_failure fallback

/-- trace: [Meta.debug] [c, d, f v, f (g b)] -/
#guard_msgs (trace) in
example (a b c d e v : Nat) : f v = c → f (g b) = d → a = e → b = e → v = g a → False := by
  grind on_failure fallback

-- arrow congruence test
example : α = α' → α'' = α' → β' = β → (α → β) = (α'' → β') := by
  grind

example (a b c : Nat) (h₁ : a = c) (h₂ : b = c) : (a = b → Nat) = (b = a → Nat) := by
  grind
