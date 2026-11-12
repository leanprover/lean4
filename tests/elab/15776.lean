import Lean

/-!
Regression tests for #15776: when unification replaces an instance-typed metavariable by an
auxiliary one (pruning `?i x := ?n` under a binder, or restricting the local context of `?i`), the
auxiliary metavariable inherits the instance-typed mark.
-/

namespace Pruning

/-!
Instance search must succeed when unifying an out-param created outside a binder prunes an
instance-typed metavariable under that binder.
-/

class C (α : Type) where
instance iC : C Unit := ⟨⟩

class Bar (α : Type) [C α] : Prop

class Out (p : outParam Prop) (α : Type) (i : C α) (x : Nat)
instance [i : C α] : Out (Bar α) α i x := ⟨⟩

class Top (q : outParam Prop)
instance [∀ x : Nat, Out q Unit iC x] : Top q := ⟨⟩

example : Top (Bar Unit) := inferInstance

end Pruning

namespace ContextRestriction

/-!
Restricting the local context of an instance-typed metavariable must not produce an unmarked
metavariable that accepts values the instance-typed check rejects.
-/

open Lean Meta

class D (α : Type) where
  val : Nat
instance iD : D Unit := ⟨0⟩

def MyUnit := Unit
instance iMy : D MyUnit := ⟨1⟩

/-- Unify `?i =?= iMy` for an instance-typed `?i : D Unit`, optionally after `?q =?= D.val ?i`
for an outer `?q` has restricted the local context of `?i`. -/
def assignInst (restrict : Bool) : MetaM Bool := do
  let q ← mkFreshExprMVar (mkConst ``Nat)
  withLocalDeclD `y (mkConst ``Nat) fun _ => do
    let i ← mkFreshExprMVar (mkApp (mkConst ``D) (mkConst ``Unit))
    i.mvarId!.markInstanceTyped
    if restrict then
      unless (← isDefEq q (mkApp2 (mkConst ``D.val) (mkConst ``Unit) i)) do
        throwError "unexpected failure of `?q =?= D.val ?i`"
      unless (← instantiateMVars i).isMVar && (← instantiateMVars i) != i do
        throwError "expected `?i` to be replaced by an auxiliary metavariable"
    isDefEq i (mkConst ``iMy)

/-- info: false -/
#guard_msgs in
#eval assignInst (restrict := false)

/-- info: false -/
#guard_msgs in
#eval assignInst (restrict := true)

end ContextRestriction

namespace Abstraction

/-!
Abstracting a free variable in the local context of an instance-typed metavariable (here via
`mkLambdaFVars`, which makes `elimMVar` assign `?i := ?n y`) must not produce an unmarked
metavariable that accepts values the instance-typed check rejects.
-/

open Lean Meta ContextRestriction

/-- Unify `?i =?= iMy` for an instance-typed `?i : D Unit` whose local context contains `y`,
optionally after abstracting `y` in `D.val ?i` has replaced `?i` by an application of an auxiliary
metavariable. -/
def assignInst (abstract : Bool) : MetaM Bool := do
  withLocalDeclD `y (mkConst ``Nat) fun y => do
    let i ← mkFreshExprMVar (mkApp (mkConst ``D) (mkConst ``Unit))
    i.mvarId!.markInstanceTyped
    if abstract then
      discard <| mkLambdaFVars #[y] (mkApp2 (mkConst ``D.val) (mkConst ``Unit) i)
      let iVal ← instantiateMVars i
      unless iVal.isApp && iVal.getAppFn.isMVar do
        throwError "expected `?i` to be replaced by an application of an auxiliary metavariable"
    isDefEq i (mkConst ``iMy)

/-- info: false -/
#guard_msgs in
#eval assignInst (abstract := false)

/-- info: false -/
#guard_msgs in
#eval assignInst (abstract := true)

end Abstraction

namespace PruneThenAssign

/-!
After pruning an instance-typed `?inst x := fun _ => ?n`, assigning a wrong instance to `?n` must be
rejected, exactly as it would be for `?inst` itself. Adapted from a test by Zongyuan Liu.
-/

open Lean Meta ContextRestriction

/-- Has no `D` instance at instance transparency, so the fallback synthesis cannot help. -/
def OtherUnit := Unit

/-- Prune `?inst : Nat → D OtherUnit` by `?q =?= D.val OtherUnit (?inst x)` for an outer `?q`, then
try `?inst x =?= iD`, where `iD : D Unit` only has the right type at default transparency. -/
def pruneThenAssign : MetaM Unit := do
  let otherUnit := mkConst ``OtherUnit
  let q ← mkFreshExprMVar (mkConst ``Nat)
  let inst ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkApp (mkConst ``D) otherUnit))
  inst.mvarId!.markInstanceTyped
  withLocalDeclD `x (mkConst ``Nat) fun x => do
    let pruned ← withConfig (fun c => { c with ctxApprox := true }) <|
      isDefEq q (mkApp2 (mkConst ``D.val) otherUnit (mkApp inst x))
    let assigned ← isDefEq (mkApp inst x) (mkConst ``iD)
    logInfo m!"pruned: {pruned}, wrong instance assigned: {assigned}"

/-- info: pruned: true, wrong instance assigned: true -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
run_meta pruneThenAssign

/-- info: pruned: true, wrong instance assigned: false -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
run_meta pruneThenAssign

end PruneThenAssign
