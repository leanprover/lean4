import Lean.Elab.Term

/-!
Test the "synthesized type class instance is not definitionally equal" error message.

When type-class resolution produces an instance that disagrees with the value already
assigned to the instance metavariable by other typing constraints, the error should
include the surrounding application and a clear indicator of which argument is the
problematic instance.
-/

class C (α : Type) where
  v : Nat

instance ic1 : C Nat := ⟨0⟩
instance ic2 : C Nat := ⟨1⟩

def myFn (α : Type) [c : C α] (x : Nat) : Nat := x + c.v

open Lean Meta Elab Term in
elab "test_mismatch" : term => do
  let type ← elabTerm (← `(C Nat)) none
  let mvar ← mkFreshExprMVar type (kind := .synthetic)
  -- Pre-assign the instance mvar to `ic1`, then trigger type-class synthesis,
  -- which (with `ic2` defined later and higher priority) produces a different value.
  mvar.mvarId!.assign (Lean.mkConst ``ic1 [])
  let app := mkAppN (Lean.mkConst ``myFn []) #[Lean.mkConst ``Nat [], mvar, Lean.mkNatLit 5]
  let _ ← synthesizeInstMVarCore mvar.mvarId! (app? := app)
  return app

#check test_mismatch
