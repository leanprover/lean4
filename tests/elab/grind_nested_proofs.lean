module
meta import Lean.Meta.Tactic.Grind
#exit -- TODO: reenable after we add support for running code in interactive mode

def f (α : Type) [Add α] (a : α) := a + a + a

open Lean Meta Grind in
meta def fallback : Fallback := do
  let nodes ← filterENodes fun e => return e.self.isAppOf ``Lean.Grind.nestedProof
  trace[Meta.debug] "{nodes.toList.map (·.self)}"
  let nodes ← filterENodes fun e => return e.self.isApp && e.self.isAppOf ``GetElem.getElem
  let [_, n, _] := nodes.toList | unreachable!
  trace[Meta.debug] "{← getEqc n.self}"
  (← get).mvarId.admit

set_option trace.Meta.debug true
set_option grind.debug true
set_option grind.debug.proofs true

/-
Recall that array access terms, such as `a[i]`, have nested proofs.
The following test relies on `grind` `nestedProof` wrapper to
detect equalities between array access terms.
-/

/--
trace: [Meta.debug] [‹i < a.size›, ‹j < a.size›, ‹j < b.size›]
[Meta.debug] [a[j], b[j], a[i]]
-/
#guard_msgs (trace) in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → a = b → False := by
  grind -mbtc on_failure fallback

/--
trace: [Meta.debug] [‹i < a.size›, ‹j < a.size›, ‹j < b.size›]
[Meta.debug] [a[j], a[i]]
-/
#guard_msgs (trace) in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → False := by
  grind -mbtc on_failure fallback

namespace Test

opaque p : Prop
axiom hp : p
opaque h : p → Prop

example : h (@Lean.Grind.nestedProof p hp) → p := by
  grind

example : h hp → p := by
  grind

end Test
