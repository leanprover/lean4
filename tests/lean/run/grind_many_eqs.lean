import Lean.Meta.Tactic.Grind

def f (a : Nat) := a + a + a
def g (a : Nat) := a + a
def h (n : Nat) : Prop :=
  match n with
  | 0   => f 0 = f 1
  | n+1 => f (n+1) = f n ∧ g (2*n + 1) = g (2*n) ∧ h n

-- Prints the equivalence class containing a `f` application
open Lean Meta Grind in
def fallback (n : Nat) : Fallback := do
  let f0 ← Grind.shareCommon (mkApp (mkConst ``f) (mkNatLit 0))
  -- The `f 0` equivalence class contains `n+1` elements
  assert! (← getEqc f0).length == n + 1
  forEachENode fun node => do
    if node.self.isAppOf ``g then
      -- Any equivalence class containing a `g`-application contains 2 elements
      assert! (← getEqc (← getRoot node.self)).length == 2
  (← get).mvarId.admit

set_option grind.debug true in
example : h 5 → False := by
  simp [h]
  grind on_failure fallback 5

set_option maxRecDepth 2048
example : h 100 → False := by
  simp [h]
  grind on_failure fallback 100
