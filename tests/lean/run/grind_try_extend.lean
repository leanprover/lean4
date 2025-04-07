import Lean

open Lean Meta Elab Tactic Try

-- Install a `TryTactic` handler for `assumption`
@[try_tactic assumption]
def evalTryApply : TryTactic := fun tac => do
  -- We just use the default implementation, but return a different tactic.
  evalAssumption tac
  `(tactic| (trace "worked"; assumption))

/-- info: Try this: · trace "worked"; assumption -/
#guard_msgs (info) in
example (h : False) : False := by
  try? (max := 1) -- at most one solution

-- `try?` uses `evalAndSuggest` the attribute `[try_tactic]` is used to extend `evalAndSuggest`.
-- Let's define our own `try?` that uses `evalAndSuggest`
elab stx:"my_try?" : tactic => do
  -- Things to try
  let toTry ← `(tactic| attempt_all | assumption | apply True | rfl)
  evalAndSuggest stx toTry

/--
info: Try these:
• · trace "worked"; assumption
• rfl
-/
#guard_msgs (info) in
example (a : Nat) (h : a = a) : a = a := by
  my_try?
