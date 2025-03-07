import Lean.Meta.Tactic.Grind

def f (α : Type) [Add α] (a : α) := a + a + a

open Lean Meta Grind in
def fallback : Fallback := do
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
info: [Meta.debug] [‹i < a.toList.length›, ‹j < a.toList.length›, ‹j < b.toList.length›]
[Meta.debug] [a[i], b[j], a[j]]
-/
#guard_msgs (info) in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → a = b → False := by
  grind on_failure fallback

/--
info: [Meta.debug] [‹i < a.toList.length›, ‹j < a.toList.length›, ‹j < b.toList.length›]
[Meta.debug] [a[i], a[j]]
-/
#guard_msgs (info) in
example (i j : Nat) (a b : Array Nat) (h1 : j < a.size) (h : j < b.size) (h2 : i ≤ j) : a[i] < a[j] + b[j] → i = j → False := by
  grind on_failure fallback
