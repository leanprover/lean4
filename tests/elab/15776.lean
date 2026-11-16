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
After instance search prunes an instance argument under a binder, the pruned instance argument still
has to have the right type at instance transparency. Adapted from a test by Zongyuan Liu and from
scenario 2 of `tests/elab/9077.lean`.

`isDefEq` unifies the out-param `r` with `G (?α x) (?q x)` and assigns `?q := fun _ => ?n`.
Then it unifies `?n : Q (Copy E)` with the instance `Q E` from the goal.
-/

class P (α : Type) where p : Nat
class Q (α : Type) extends P α where

@[implicit_reducible]
def Copy (α : Type) := α

structure G (α : Type) (q : Q α) : Prop where

class Out (p : outParam Prop) (α : Type) (q : Q α) (x : Nat)
instance [q : Q α] : Out (G α q) α q x := ⟨⟩

class Top (E : Type) (r : outParam Prop)
instance [iQ : Q E] [∀ x : Nat, Out r (Copy E) iQ x] : Top E r := ⟨⟩

/-- info: instTopOfOutCopy -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
variable (E : Type) [Q E] in
#synth Top E _

/-! Without a `Q (Copy E)` instance, `isDefEq` must reject `?n := (iQ : Q E)`. -/

/--
error: failed to synthesize
  Top E ?m.1

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
variable (E : Type) [Q E] in
#synth Top E _

/-!
With a `Q (Copy E)` instance, `isDefEq` synthesizes it for `?n` after rejecting `iQ`. This needs
`?n` to be instance-typed: otherwise `isDefEq` rejects the pruning step already.
-/

instance qCopy [Q E] : Q (Copy E) := ‹Q E›

/-- info: instTopOfOutCopy -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
variable (E : Type) [Q E] in
#synth Top E _

end PruneThenAssign

namespace MVarSelf

/-!
Solving `?inst x =?= ?inst y` by `?inst := fun _ => ?n` must succeed for an instance-typed `?inst`,
and assigning a wrong instance to `?n` afterwards must be rejected, exactly as it would be for
`?inst` itself.
-/

open Lean Meta ContextRestriction

/-- Has no `D` instance at instance transparency, so the fallback synthesis cannot help. -/
def OtherUnit := Unit

/-- Unify `?inst x =?= ?inst y` for `?inst : Nat → D OtherUnit`, then try `?inst x =?= iD`, where
`iD : D Unit` only has the right type at default transparency. -/
def selfThenAssign : MetaM Unit := do
  let otherUnit := mkConst ``OtherUnit
  let inst ← mkFreshExprMVar (← mkArrow (mkConst ``Nat) (mkApp (mkConst ``D) otherUnit))
  inst.mvarId!.markInstanceTyped
  withLocalDeclD `x (mkConst ``Nat) fun x => withLocalDeclD `y (mkConst ``Nat) fun y => do
    let solved ← withConfig (fun c => { c with constApprox := true }) <|
      isDefEq (mkApp inst x) (mkApp inst y)
    let assigned ← isDefEq (mkApp inst x) (mkConst ``iD)
    logInfo m!"solved: {solved}, wrong instance assigned: {assigned}"

/-- info: solved: true, wrong instance assigned: true -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
run_meta selfThenAssign

/-- info: solved: true, wrong instance assigned: false -/
#guard_msgs in
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true in
run_meta selfThenAssign

end MVarSelf
