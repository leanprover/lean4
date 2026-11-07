/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module


prelude
public import Lean.Meta.Basic
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.SplitIf
import Lean.Meta.Tactic.Contradiction

/-!
This module contains helpers useful to prove unfolding and/or equational theorems.
-/

namespace Lean.Elab.Eqns
open Meta

public def simpMatch? (mvarId : MVarId) : MetaM (Option MVarId) := do
  let mvarId' ← Split.simpMatchTarget mvarId
  if mvarId != mvarId' then return some mvarId' else return none

/--
Simplify `if-then-expression`s in the goal target.
If `useNewSemantics` is `true`, the flag `backward.split` is ignored.
-/
public def simpIf? (mvarId : MVarId) (useNewSemantics := false) : MetaM (Option MVarId) := do
  let mvarId' ← simpIfTarget mvarId (useDecide := true) (useNewSemantics := useNewSemantics)
  if mvarId != mvarId' then return some mvarId' else return none

/--
Try to close goal using `rfl` with smart unfolding turned off.

If both sides are applications of the same function in `declNames`, the proof is `Eq.refl` of the
left-hand side unfolded once, instead of `Eq.refl lhs`. Example (#15987):
```
def f : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => f n ((x * 1103515245) % 5)

theorem f.eq_2 (x n : Nat) : f (n+1) x = f n (x * 1103515245 % 5)
```
To check `Eq.refl (f (n+1) x)`, the kernel must show `f (n+1) x =?= f n (x * 1103515245 % 5)`.
Since both sides are applications of `f`, it first tries to show that the arguments are
definitionally equal, starting with the last one: `x =?= x * 1103515245 % 5`. This forces it to
reduce `x * 1103515245` with a free `x`, which unfolds `Nat.mul` once per unit of `1103515245`, and
fails with deep recursion. That comparison can never succeed anyway, since a recursive call is on
a smaller argument (here `n` vs `n+1`). The proof `Eq.refl (Nat.brecOn (n+1) f._f x)` avoids it:
the left-hand side is no longer an application of `f`, so the kernel unfolds both sides instead.
-/
public def tryURefl (mvarId : MVarId) (declNames : Array Name := #[]) : MetaM Bool :=
  withOptions (smartUnfolding.set · false) do
    try
      mvarId.withContext do
        let target ← mvarId.getType'
        let_expr f@Eq α lhs rhs := target | mvarId.refl
        let lhs ← instantiateMVars lhs
        let rhs ← instantiateMVars rhs
        let .const declName _ := lhs.getAppFn | mvarId.refl
        unless declNames.contains declName && rhs.isAppOf declName do mvarId.refl; return
        let some lhs' ← delta? lhs (· == declName) | mvarId.refl
        unless (← isDefEq lhs rhs) do throwError "not definitionally equal"
        mvarId.assign (mkApp2 (mkConst ``Eq.refl f.constLevels!) α lhs')
      return true
    catch _ => return false

/-- Delta reduce the equation left-hand-side -/
public def deltaLHS (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHS mvarId "equality expected"
  let some lhs ← delta? lhs | throwTacticEx `deltaLHS mvarId "failed to delta reduce lhs"
  mvarId.replaceTargetDefEq (← mkEq lhs rhs)

public def tryContradiction (mvarId : MVarId) : MetaM Bool := do
  mvarId.contradictionCore { genDiseq := true }

partial def whnfAux (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  let f := e.getAppFn
  match f with
  | .proj _ _ s => return mkAppN (f.updateProj! (← whnfAux s)) e.getAppArgs
  | _ => return e

/-- Apply `whnfR` to lhs, return `none` if `lhs` was not modified -/
public def whnfReducibleLHS? (mvarId : MVarId) : MetaM (Option MVarId) := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | return none
  let lhs' ← whnfAux lhs
  if lhs' != lhs then
    return some (← mvarId.replaceTargetDefEq (← mkEq lhs' rhs))
  else
    return none

end Lean.Elab.Eqns
