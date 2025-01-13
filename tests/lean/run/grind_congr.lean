import Lean

def f (a : Nat) := a + a + a
def g (a : Nat) := a + a

-- Prints the equivalence class containing a `f` application
open Lean Meta Grind in
def fallback : Fallback := do
  let #[n, _] ← filterENodes fun e => return e.self.isAppOf ``f | unreachable!
  let eqc ← getEqc n.self
  trace[Meta.debug] eqc
  (← get).mvarId.admit

set_option trace.Meta.debug true
set_option grind.debug true
set_option grind.debug.proofs true

/--
info: [Meta.debug] [d, f b, c, f a]
-/
#guard_msgs (info) in
example (a b c d : Nat) : a = b → f a = c → f b = d → False := by
  grind on_failure fallback

/--
info: [Meta.debug] [d, f b, c, f a]
-/
#guard_msgs (info) in
example (a b c d : Nat) : f a = c → f b = d → a = b → False := by
  grind on_failure fallback

/--
info: [Meta.debug] [d, f (g b), c, f (g a)]
-/
#guard_msgs (info) in
example (a b c d e : Nat) : f (g a) = c → f (g b) = d → a = e → b = e → False := by
  grind on_failure fallback

/--
info: [Meta.debug] [d, f (g b), c, f v]
-/
#guard_msgs (info) in
example (a b c d e v : Nat) : f v = c → f (g b) = d → a = e → b = e → v = g a → False := by
  grind on_failure fallback
