/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Assert
import Lean.Meta.Match.CaseValues

namespace Lean.Meta

structure CaseArraySizesSubgoal where
  mvarId : MVarId
  elems  : Array FVarId := #[]
  diseqs : Array FVarId := #[]
  subst  : FVarSubst := {}
  deriving Inhabited

def getArrayArgType (a : Expr) : MetaM Expr := do
  let aType ← inferType a
  let aType ← whnfD aType
  unless aType.isAppOfArity ``Array 1 do
    throwError "array expected{indentExpr a}"
  pure aType.appArg!

private def mkArrayGetLit (a : Expr) (i : Nat) (n : Nat) (h : Expr) : MetaM Expr := do
  let lt    ← mkLt (mkRawNatLit i) (mkRawNatLit n)
  let ltPrf ← mkDecideProof lt
  mkAppM `Array.getLit #[a, mkRawNatLit i, h, ltPrf]

private partial def introArrayLit (mvarId : MVarId) (a : Expr) (n : Nat) (xNamePrefix : Name) (aSizeEqN : Expr) : MetaM MVarId := do
  let α ← getArrayArgType a
  let rec loop (i : Nat) (xs : Array Expr) (args : Array Expr) := do
    if i < n then
      withLocalDeclD (xNamePrefix.appendIndexAfter (i+1)) α fun xi => do
        let xs := xs.push xi
        let ai ← mkArrayGetLit a i n aSizeEqN
        let args := args.push ai
        loop (i+1) xs args
    else
      let xsLit     ← mkArrayLit α xs.toList
      let aEqXsLit  ← mkEq a xsLit
      let aEqLitPrf ← mkAppM ``Array.toArrayLit_eq #[a, mkRawNatLit n, aSizeEqN]
      withLocalDeclD `hEqALit aEqXsLit fun heq => do
        let target    ← mvarId.getType
        let newTarget ← mkForallFVars (xs.push heq) target
        pure (newTarget, args.push aEqLitPrf)
  let (newTarget, args) ← loop 0 #[] #[]
  let tag ← mvarId.getTag
  let newMVar   ← mkFreshExprSyntheticOpaqueMVar newTarget tag
  mvarId.assign (mkAppN newMVar args)
  pure newMVar.mvarId!

/--
  Split goal `... |- C a` into sizes.size + 1 subgoals
  1) `..., x_1 ... x_{sizes[0]} |- C #[x_1, ... x_{sizes[0]}]`
  ...
  n) `..., x_1 ... x_{sizes[n-1]}  |- C #[x_1, ..., x_{sizes[n-1]}]`
  n+1) `..., (h_1 : a.size != sizes[0]), ..., (h_n : a.size != sizes[n-1]) |- C a`
  where `n = sizes.size` -/
def caseArraySizes (mvarId : MVarId) (fvarId : FVarId) (sizes : Array Nat) (xNamePrefix := `x) (hNamePrefix := `h) : MetaM (Array CaseArraySizesSubgoal) :=
  mvarId.withContext do
    let a := mkFVar fvarId
    let aSize ← mkAppM `Array.size #[a]
    let mvarId ← mvarId.assertExt `aSize (mkConst `Nat) aSize
    let (aSizeFVarId, mvarId) ← mvarId.intro1
    let (hEq, mvarId) ← mvarId.intro1
    let subgoals ← caseValues mvarId aSizeFVarId (sizes.map mkRawNatLit) hNamePrefix
    subgoals.mapIdxM fun i subgoal => do
      let subst  := subgoal.subst
      let mvarId := subgoal.mvarId
      let hEqSz  := (subst.get hEq).fvarId!
      if h : i < sizes.size then
         let n := sizes[i]
         let mvarId ← mvarId.clear subgoal.newHs[0]!
         let mvarId ← mvarId.clear (subst.get aSizeFVarId).fvarId!
         mvarId.withContext do
           let hEqSzSymm ← mkEqSymm (mkFVar hEqSz)
           let mvarId ← introArrayLit mvarId a n xNamePrefix hEqSzSymm
           let (xs, mvarId)  ← mvarId.introN n
           let (hEqLit, mvarId) ← mvarId.intro1
           let mvarId ← mvarId.clear hEqSz
           let (subst, mvarId) ← substCore mvarId hEqLit false subst
           pure { mvarId := mvarId, elems := xs, subst := subst }
      else
         let (subst, mvarId) ← substCore mvarId hEq false subst
         let diseqs := subgoal.newHs.map fun fvarId => (subst.get fvarId).fvarId!
         pure { mvarId := mvarId, diseqs := diseqs, subst := subst }

end Lean.Meta
