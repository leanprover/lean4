/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.KAbstract
import Lean.Meta.Check
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply
import Lean.Meta.BinderNameHint

namespace Lean.Meta

/-- Modifies the pattern `lhs` by clearing all instance implicit arguments that can be cleared. -/
private partial def relaxPattern (lhs : Expr) : MetaM Expr := do
  let rec relaxApp (f : Expr) (args : Array Expr) : MetaM Expr := do
    if args.isEmpty then
      return f
    else
      let mut args := args
      let info ← getFunInfoNArgs f args.size
      let mut backDeps := info.resultDeps
      for i' in [0:info.getArity] do
        let i := info.getArity - i' - 1
        if info.paramInfo[i']!.binderInfo.isInstImplicit && i ∉ backDeps then
          args := args.set! i <| ← mkFreshExprMVar (← inferType args[i]!)
        else
          backDeps := backDeps ++ info.paramInfo[i']!.backDeps
      relaxApp (mkAppN f args[0:info.getArity]) args[info.getArity:]
  Meta.transform lhs (skipConstInApp := true)
    (post := fun e => do
      if e.isApp then
        e.withApp fun f args => return .done <| ← relaxApp f args
      else
        return .continue)

structure RewriteResult where
  eNew     : Expr
  eqProof  : Expr
  mvarIds  : List MVarId -- new goals

/--
Rewrite expression `e` in the context of metavariable `mvarId` using the proof `heq` of an equality or iff.
- `mvarId` is the context to use, and it is used when reporting errors.
- `e` is the expression to rewrite.
- `heq` is the proof whose type is the rewrite rule.
- If `symm` is true, then reverses the rewrite.
- If `interactive` is true, then tries to make nicer error messages.
-/
def _root_.Lean.MVarId.rewrite (mvarId : MVarId) (e : Expr) (heq : Expr)
    (symm : Bool := false) (config := { : Rewrite.Config }) (interactive := false) : MetaM RewriteResult :=
  mvarId.withContext do
    mvarId.checkNotAssigned `rewrite
    let heqIn := heq
    let heqType ← instantiateMVars (← inferType heq)
    let (newMVars, binderInfos, heqType) ← forallMetaTelescopeReducing heqType
    let heq := mkAppN heq newMVars
    let (heq, heqType, α, lhs, rhs) ← processRule heq heqType
    if lhs.getAppFn.isMVar then
      throwTacticEx `rewrite mvarId m!"pattern is a metavariable{indentExpr lhs}\nfrom equation{indentExpr heqType}"
    let e ← instantiateMVars e
    let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs config.occs
    unless eAbst.hasLooseBVars do
      if interactive then
        if let some lhs' ← observing? (relaxPattern lhs) then
          let eAbst ← withConfig (fun oldConfig => { config, oldConfig with }) <| kabstract e lhs' config.occs
          if eAbst.hasLooseBVars then
            -- todo: do structural defeq? list missing instances? try partial postprocessAppMVars?
            let (lhs, lhs') ← addPPExplicitToExposeDiff lhs lhs'
            throwTacticEx `rewrite mvarId m!"\
              did not find an exact match for the pattern in the target expression, found\
              {indentExpr lhs'}\
              but expecting\
              {indentExpr lhs}"
      throwTacticEx `rewrite mvarId m!"did not find an instance of the pattern{indentExpr lhs}\nin the target expression"
    -- construct rewrite proof
    let eNew := eAbst.instantiate1 rhs
    let eNew ← instantiateMVars eNew
    let eNew ← if rhs.hasBinderNameHint then eNew.resolveBinderNameHint else pure eNew
    let eType ← inferType e
    let motive := Lean.mkLambda `_a BinderInfo.default α eAbst
    try
      check motive
    catch ex =>
      throwTacticEx `rewrite mvarId m!"\
        motive is not type correct:{indentD motive}\nError: {ex.toMessageData}\
        \n\n\
        Explanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. \
        First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, \
        with the property that 'm a' is definitionally equal to 'e'. \
        Third, we observe that '{.ofConstName ``congrArg}' implies that 'm a = m b', which can be used with lemmas such as '{.ofConstName ``Eq.mpr}' to change the goal. \
        However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\
        \n\n\
        Possible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, \
        or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies \
        (these tactics can handle proofs and '{.ofConstName ``Decidable}' instances whose types depend on the rewritten term, \
        and 'simp' can apply user-defined '@[congr]' theorems as well)."
    unless (← withLocalDeclD `_a α fun a => do isDefEq (← inferType (eAbst.instantiate1 a)) eType) do
      -- NB: using motive.arrow? would disallow motives where the dependency
      -- can be reduced away
      throwTacticEx `rewrite mvarId m!"motive is dependent{indentD motive}"
    let u1 ← getLevel α
    let u2 ← getLevel eType
    let eqPrf := mkApp6 (.const ``congrArg [u1, u2]) α eType lhs rhs motive heq
    postprocessAppMVars `rewrite mvarId newMVars binderInfos
      (synthAssignedInstances := !tactic.skipAssignedInstances.get (← getOptions))
    let newMVarIds ← newMVars.map Expr.mvarId! |>.filterM fun mvarId => not <$> mvarId.isAssigned
    let otherMVarIds ← getMVarsNoDelayed heqIn
    let otherMVarIds := otherMVarIds.filter (!newMVarIds.contains ·)
    let newMVarIds := newMVarIds ++ otherMVarIds
    pure { eNew := eNew, eqProof := eqPrf, mvarIds := newMVarIds.toList }
where
  processRule (heq heqType : Expr) : MetaM (Expr × Expr × Expr × Expr × Expr) := do
    let (heq, heqType) ←
      match heqType.iff? with
      | some (lhs, rhs) =>
        let heqType ← mkEq lhs rhs
        let heq := mkApp3 (mkConst `propext) lhs rhs heq
        pure (heq, heqType)
      | none =>
        pure (heq, heqType)
    match (← matchEq? heqType) with
    | none => throwTacticEx `rewrite mvarId m!"only equalities and iffs can be used as rewrite rules, but the type is{indentExpr heqType}\n"
    | some (α, lhs, rhs) =>
      if symm then
        let heq ← mkEqSymm heq
        let heqType ← mkEq rhs lhs
        pure (heq, heqType, α, rhs, lhs)
      else
        pure (heq, heqType, α, lhs, rhs)

end Lean.Meta
