import Lean.Meta.Tactic.Grind

def g {α : Sort u} (a : α) := a

open Lean Meta Grind in
def fallback : Fallback := do
  let nodes ← filterENodes fun e => return e.self.isAppOf ``g
  trace[Meta.debug] "{nodes.toList.map (·.self)}"
  (← get).mvarId.admit

-- `grind` final state must contain only two `g`-applications
set_option trace.Meta.debug true in
/--
info: [Meta.debug] [g (a, b), g (g (a, b))]
-/
#guard_msgs (info) in
example {β : Type v} {α : Type u} (a c : α) (b d : β) : g.{max u v + 1} (a, b) = (c, d) → g (g.{max (u+1) (v+1)} (a, b)) = (c, d) → False := by
  grind on_failure fallback
