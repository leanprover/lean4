module
public meta import Lean.Elab.Command

/-!
Tests that the exported view of a theorem that was realized only inside a proof is an axiom, as it is
for a theorem realized on the main environment branch.
-/

open Lean Elab Command

/-- Logs the kind of the exported view of the given declaration. -/
elab "#exported_kind " id:ident : command => do
  let env := (← getEnv).setExporting true
  let some info := env.find? id.getId
    | throwError "`{id.getId}` is not exported"
  logInfo m!"{if info.isAxiom then "axiom" else if info.isTheorem then "theorem" else "other"}"

public def f (n : Nat) (_h : n > 0) : Nat := n

-- `simp` realizes `f.congr_simp` here
public theorem foo (a : Nat) (h : a + 0 > 0) : f (a + 0) h = f a (by simpa using h) := by
  simp

/-- info: axiom -/
#guard_msgs in
#exported_kind f.congr_simp

set_option Elab.async false in
public def g (n : Nat) (_h : n > 0) : Nat := n

set_option Elab.async false in
public theorem bar (a : Nat) (h : a + 0 > 0) : g (a + 0) h = g a (by simpa using h) := by
  simp

/-- info: axiom -/
#guard_msgs in
#exported_kind g.congr_simp
