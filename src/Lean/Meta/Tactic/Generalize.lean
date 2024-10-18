/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Revert

namespace Lean.Meta

/-- The `generalize` tactic takes arguments of the form `h : e = x` -/
structure GeneralizeArg where
  expr   : Expr
  xName? : Option Name := none
  hName? : Option Name := none
  deriving Inhabited

/--
Telescopic `generalize` tactic. It can simultaneously generalize many terms.
It uses `kabstract` to occurrences of the terms that need to be generalized.
-/
private partial def generalizeCore (mvarId : MVarId) (args : Array GeneralizeArg)
    (transparency : TransparencyMode) : MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `generalize
    let tag ← mvarId.getTag
    let target ← instantiateMVars (← mvarId.getType)
    let rec go (i : Nat) : MetaM Expr := do
      if _h : i < args.size then
        let arg := args[i]
        let e ← instantiateMVars arg.expr
        let eType ← instantiateMVars (← inferType e)
        let type ← go (i+1)
        let xName ← if let some xName := arg.xName? then pure xName else mkFreshUserName `x
        return Lean.mkForall xName BinderInfo.default eType
          (← withTransparency transparency <| kabstract type e)
      else
        return target
    let targetNew ← go 0
    unless (← isTypeCorrect targetNew) do
      throwTacticEx `generalize mvarId m!"result is not type correct{indentExpr targetNew}"
    let es := args.map (·.expr)
    if !args.any fun arg => arg.hName?.isSome then
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      mvarId.assign (mkAppN mvarNew es)
      mvarNew.mvarId!.introNP args.size
    else
      let (rfls, targetNew) ← forallBoundedTelescope targetNew args.size fun xs type => do
        let rec go' (i : Nat) : MetaM (List Expr × Expr) := do
          if _h : i < xs.size then
            let arg := args[i]!
            if let some hName := arg.hName? then
              let xType ← inferType xs[i]
              let e ← instantiateMVars arg.expr
              let eType ← instantiateMVars (← inferType e)
              let (hType, r) ← if (← isDefEq xType eType) then
                pure (← mkEq e xs[i], ← mkEqRefl e)
              else
                pure (← mkHEq e xs[i], ← mkHEqRefl e)
              let (rs, type) ← go' (i+1)
              return (r :: rs, mkForall hName BinderInfo.default hType type)
            else
              go' (i+1)
          else
            return ([], type)
        let (rfls, type) ← go' 0
        return (rfls, ← mkForallFVars xs type)
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      mvarId.assign (mkAppN (mkAppN mvarNew es) rfls.toArray)
      mvarNew.mvarId!.introNP (args.size + rfls.length)

/-
Remark: we use `TransparencyMode.instances` as the default setting at `generalize`
and `generalizeHyp` to avoid excessive resource usage.

**Motivation:**
The `kabstract e p` operation is widely used, for instance, in the `generalize` tactic.
It operates by taking an expression `e` and a pattern (i.e., an expression containing metavariables)
and employs keyed-matching to identify and abstract instances of `p` within `e`.
For example, if `e` is `a + (2 * (b + c))` and `p` is `2 * ?m`, the resultant expression
would be `a + #0`, where `#0` represents a loose bound variable.

This matching process is not merely syntactic; it also considers reduction. It's impractical
to attempt matching each sub-term with `p`; therefore, only sub-terms sharing the same "root"
symbol are evaluated. For instance, with the pattern `2 * ?m`, only sub-terms with the
root `*` are considered. Matching is executed using the definitionally equality test
(i.e., `isDefEq`).

The `generalize` tactic employs `kabstract` and defaults to standard reducibility.
Hence, the `isDefEq` operations invoked by `kabstract` can become highly resource-intensive
and potentially trigger "max recursion depth reached" errors, as observed in issue #3524.
This issue was isolated by @**Kim Morrison** with the following example:
```
example (a : Nat) : ((2 ^ 7) + a) - 2 ^ 7 = 0 := by
  generalize 0 - 0 = x
```
In this scenario, `kabstract` triggers a "max recursion depth reached" error while
testing whether `((2 ^ 7) + a) - 2 ^ 7` is definitionally equal to `0 - 0`.
Note that the term `((2 ^ 7) + a) - 2 ^ 7` is not ground.
We believe most users find the error message to be uninformative and unexpected.
To fix this issue, we decided to use `TransparencyMode.instances` as the default setting.

Kyle Miller has performed the following analysis on the potential impact of the
changes on Mathlib (2024-03-02).

There seem to be just 130 cases of generalize in Mathlib, and after looking through a
good number of them, they seem to come in just two types:

- Ones where it looks like reducible+instance transparency should work, where in
  particular there is nothing obvious being reduced, and
- Ones that don't make use of the `kabstract` feature at all (it's being used like a
  `have` that introduces an equality for rewriting).

That wasn't a systematic review of generalize though. It's possible changing the
transparency settings would break things, but in my opinion it would be better
if generalize weren't used for unfolding things.
-/

@[inherit_doc generalizeCore]
def _root_.Lean.MVarId.generalize (mvarId : MVarId) (args : Array GeneralizeArg)
    (transparency := TransparencyMode.instances) : MetaM (Array FVarId × MVarId) :=
  generalizeCore mvarId args transparency

/--
Extension of `generalize` to support generalizing within specified hypotheses.
The `hyps` array contains the list of hypotheses within which to look for occurrences
of the generalizing expressions.
-/
def _root_.Lean.MVarId.generalizeHyp (mvarId : MVarId) (args : Array GeneralizeArg) (hyps : Array FVarId := #[])
    (fvarSubst : FVarSubst := {}) (transparency := TransparencyMode.instances) : MetaM (FVarSubst × Array FVarId × MVarId) := do
  if hyps.isEmpty then
    -- trivial case
    return (fvarSubst, ← mvarId.generalize args transparency)
  let args ← args.mapM fun arg => return { arg with expr := ← instantiateMVars arg.expr }
  let hyps ← hyps.filterM fun h => do
    let type ← instantiateMVars (← h.getType)
    args.anyM fun arg => return (← withTransparency transparency <| kabstract type arg.expr).hasLooseBVars
  let (reverted, mvarId) ← mvarId.revert hyps true
  let (newVars, mvarId) ← mvarId.generalize args transparency
  let (reintros, mvarId) ← mvarId.introNP reverted.size
  let fvarSubst := Id.run do
    let mut subst : FVarSubst := fvarSubst
    for h in reverted, reintro in reintros do
      subst := subst.insert h (mkFVar reintro)
    pure subst
  return (fvarSubst, newVars, mvarId)

end Lean.Meta
