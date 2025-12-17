/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

module

prelude
public import Lean.Meta.Basic
import Lean.AddDecl
import Lean.Meta.Constructions.SparseCasesOn
import Lean.Meta.AppBuilder
import Lean.Meta.HasNotBit
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Refl

namespace Lean.Meta

/--
Given a sparseCasesOn, creates an equational theorem for the else-case.
-/
public def getSparseCasesOnEq (sparseCasesOnName : Name) : MetaM Name := do
  let thmName := sparseCasesOnName.str "else_eq"
  realizeConst sparseCasesOnName thmName (realize thmName)
  return thmName
where
  realize thmName := do
    let some casesOnInfo ← getSparseCasesOnInfo sparseCasesOnName
      | throwError "mkSparseCasesOnEq: {sparseCasesOnName} is not a sparse casesOn combinator"
    let info ← getConstVal sparseCasesOnName
    let us := info.levelParams.map mkLevelParam
    forallTelescope info.type fun xs _ => do
      let otherAlt := xs.back!
      forallTelescope (← inferType otherAlt) fun hyps _ => do
        assert! hyps.size = 1
        let hyp := hyps[0]!
        let lhs := mkAppN (mkConst sparseCasesOnName us) xs
        let rhs := mkAppN otherAlt hyps
        let eq ← mkEq lhs rhs
        let val ← mkFreshExprSyntheticOpaqueMVar eq
        let mvarId := val.mvarId!
        -- We separate `hasNotBit mask x.ctorIdx` into `hasNotBit mask i` and `i = x.ctorIdx`
        -- to prevent the kernel from running into #11181
        -- (Even with #11181 fixes this may be necessary to avoid the kernel from reducing
        -- `hasNotBit` without native nat computation)
        let_expr Nat.hasNotBit mask ctorIdxApp := (← inferType hyp) | throwError "mkSparseCasesOnEq: unexpected hyp type {← inferType hyp}"
        -- Simulate `generalize h : x.ctorIdx = i`
        let mvarId ← mvarId.assertExt `idx (type := mkConst ``Nat) (val := ctorIdxApp) `hidx
        let (ctorIdxApp, mvarId) ← mvarId.intro1P
        let (ctorIdxAppEq, mvarId) ← mvarId.intro1P
        mvarId.withContext do
        let hyp'Type := mkApp2 (mkConst ``Nat.hasNotBit) mask (mkFVar ctorIdxApp)
        let hyp'Val ← do
          let val ← mkFreshExprSyntheticOpaqueMVar hyp'Type
          let (subst, hypMVarId) ← substEq val.mvarId! ctorIdxAppEq
          hypMVarId.assign (hyp.applyFVarSubst subst)
          pure val
        let (hyp', mvarId) ← mvarId.note `h hyp'Val hyp'Type
        -- The original hyp is still mentioned, so we cannot
        --   let mvarId ← mvarId.clear hyp.fvarId!
        -- but that is ok.
        let subgoals ← mvarId.cases xs[casesOnInfo.majorPos]!.fvarId!
        subgoals.forM fun s => s.mvarId.withContext do
          assert! s.ctorName.isSome
          if s.ctorName.get! ∈ casesOnInfo.insterestingCtors then
            let hyp := s.subst.get hyp'
            let ctorIdxAppEq := s.subst.get ctorIdxAppEq
            let (subst, mvarId) ← substEq s.mvarId ctorIdxAppEq.fvarId!
            let hyp := hyp.applyFVarSubst subst
            mvarId.withContext do
              let some prf ← refutableHasNotBit? (← inferType hyp)
                | throwError m!"mkSparseCasesOnEq: not refutable {← inferType hyp}"
              mvarId.assign (← mkAbsurd (← mvarId.getType) prf hyp)
          else
            s.mvarId.refl
        let val ← instantiateMVars val
        let type ← mkForallFVars (xs ++ hyps) eq
        let val ← mkLambdaFVars (xs ++ hyps) val

        addDecl (.thmDecl {
          name := thmName
          levelParams := info.levelParams
          type := type
          value := val
        })

private def isName (env : Environment) (n : Name) : Bool :=
  if let .str p "else_eq" := n then
    (getSparseCasesOnInfoCore env p).isSome
  else
    false

builtin_initialize registerReservedNamePredicate isName

builtin_initialize registerReservedNameAction fun name => do
  if isName (← getEnv) name then
    let name' ← MetaM.run' <| getSparseCasesOnEq name.getPrefix
    assert! name = name'
    return true
  else
    return false
