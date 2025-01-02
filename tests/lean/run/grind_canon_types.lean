import Lean.Meta.Tactic.Grind

def g (s : Type) := s
def f (a : α) := a

open Lean Meta Grind in
def fallback : Fallback := do
  let nodes ← filterENodes fun e => return e.self.isAppOf ``f
  logInfo (nodes.toList.map (·.self))
  (← get).mvarId.admit

set_option pp.explicit true
/--
info: [@f Nat a, @f Nat b]
-/
#guard_msgs (info) in
example (a b c d : Nat) : @f Nat a = b → @f (g Nat) a = c → @f (g Nat) b = d → a = b → False := by
  -- State should have only two `f`-applications: `@f Nat a`, `@f Nat b`
  -- Note that `@f (g Nat) b` has been canonicalized to `@f Nat b`.
  -- Thus, if `a` and `b` equivalence classes are merged, `grind` can still detect that
  -- `@f Nat a` and `@f Nat b` are equal too.
  grind on_failure fallback
