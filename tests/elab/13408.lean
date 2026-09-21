module

import Lean
/-!
# Auxiliary definitions and let-variables

`Closure.mkValueTypeClosure` must not lambda abstract a let-variable whose value is needed for the
value of the auxiliary declaration to have the given type.
See https://github.com/leanprover/lean4/issues/13408
-/

open Lean Meta

/-- Prints the type of the constants whose name ends with `suffix`. -/
def printAux (suffix : String) : MetaM Unit := do
  for (n, c) in (← getEnv).constants.map₂.toList do
    if n.toString.endsWith suffix then
      logInfo m!"{suffix} : {c.type}"

example : True := by
  let E : Type := id Nat
  let hE : Inhabited E := inferInstanceAs (Inhabited Nat)
  trivial

def MyNat := Nat

example : True := by
  let n : Nat := 3
  let s : Type := Fin n
  let : Inhabited s := inferInstanceAs (Inhabited (Fin 3))
  trivial

example : True := by
  let E : Type := id MyNat
  let : Inhabited E := inferInstanceAs (Inhabited Nat)
  trivial

instance : Add MyNat := inferInstanceAs (Add Nat)

example : True := by
  let E : Type := MyNat
  let : Add E := inferInstanceAs (Add Nat)
  trivial

/-! The let-variable is kept as a `let`, it is not zeta-delta expanded. -/

theorem foo : True := by
  let E : Type := id Nat
  let hE : Inhabited E := inferInstanceAs (Inhabited Nat)
  trivial

/-- info: foo._aux_1_1 : let E := id Nat;
E -/
#guard_msgs in
run_meta printAux "foo._aux_1_1"

/-!
Direct use of `mkAuxDefinition`, where `type` and `value` contain metavariables.
Here `v : E` holds by unfolding `E := ?α`, but `isDefEq` cannot establish it without assigning
metavariables, so all let-variables are kept as `let`s. The metavariables must not be assigned.
-/

/-- info: testAux : (_x_1 : Type) →
  _x_1 →
    let E := _x_1;
    E -/
#guard_msgs in
run_meta do
  let α ← mkFreshExprMVar (mkSort (.succ .zero))
  withLetDecl `E (mkSort (.succ .zero)) α fun e => do
    let v ← mkFreshExprMVar α
    discard <| mkAuxDefinition `testAux e v (compile := false)
    unless !(← α.mvarId!.isAssigned) && !(← v.mvarId!.isAssigned) do
      throwError "metavariables were assigned"
  printAux "testAux"

/-! Let-variables that are not needed for `value : type` are still lambda abstracted. -/

/-- info: testAux2 : Nat →
  let E := id Nat;
  E -/
#guard_msgs in
run_meta do
  withLetDecl `n (mkConst ``Nat) (mkNatLit 3) fun n => do
  withLetDecl `E (mkSort (.succ .zero))
      (mkApp2 (mkConst ``id [.succ (.succ .zero)]) (mkSort (.succ .zero)) (mkConst ``Nat)) fun e => do
    discard <| mkAuxDefinition `testAux2 e n (compile := false)
  printAux "testAux2"
