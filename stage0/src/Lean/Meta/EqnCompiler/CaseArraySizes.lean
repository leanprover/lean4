/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Assert
import Lean.Meta.EqnCompiler.CaseValues

namespace Lean
namespace Meta

structure CaseArraySizesSubgoal :=
(mvarId : MVarId)
(elems  : Array FVarId := #[])
(diseqs : Array FVarId := #[])
(subst  : FVarSubst := {})

instance CaseArraySizesSubgoal.inhabited : Inhabited CaseArraySizesSubgoal :=
⟨{ mvarId := arbitrary _ }⟩

def getArrayArgType (a : Expr) : MetaM Expr := do
aType ← inferType a;
aType ← whnfD aType;
unless (aType.isAppOfArity `Array 1) $
  throwError ("array expected" ++ indentExpr a);
pure aType.appArg!

private def mkArrayGetLit (a : Expr) (i : Nat) (n : Nat) (h : Expr) : MetaM Expr := do
lt    ← mkLt (mkNatLit i) (mkNatLit n);
ltPrf ← mkDecideProof lt;
mkAppM `Array.getLit #[a, mkNatLit i, h, ltPrf]

private partial def introArrayLitAux (mvarId : MVarId) (α : Expr) (a : Expr) (n : Nat) (xNamePrefix : Name) (aSizeEqN : Expr)
    : Nat → Array Expr → Array Expr → MetaM (Expr × Array Expr)
| i, xs, args =>
  if i < n then do
    withLocalDecl (xNamePrefix.appendIndexAfter (i+1)) α BinderInfo.default fun xi => do
      let xs := xs.push xi;
      ai ← mkArrayGetLit a i n aSizeEqN;
      let args := args.push ai;
      introArrayLitAux (i+1) xs args
  else do
    xsLit     ← mkArrayLit α xs.toList;
    aEqXsLit  ← mkEq a xsLit;
    aEqLitPrf ← mkAppM `Array.toArrayLitEq #[a, mkNatLit n, aSizeEqN];
    withLocalDecl `hEqALit aEqXsLit BinderInfo.default fun heq => do
      target    ← getMVarType mvarId;
      newTarget ← mkForall (xs.push heq) target;
      pure (newTarget, args.push aEqLitPrf)

private partial def introArrayLit (mvarId : MVarId) (a : Expr) (n : Nat) (xNamePrefix : Name) (aSizeEqN : Expr) : MetaM MVarId := do
α ← getArrayArgType a;
(newTarget, args) ← introArrayLitAux mvarId α a n xNamePrefix aSizeEqN 0 #[] #[];
tag ← getMVarTag mvarId;
newMVar   ← mkFreshExprSyntheticOpaqueMVar newTarget tag;
assignExprMVar mvarId (mkAppN newMVar args);
pure newMVar.mvarId!

/--
  Split goal `... |- C a` into sizes.size + 1 subgoals
  1) `..., x_1 ... x_{sizes[0]} |- C #[x_1, ... x_{sizes[0]}]`
  ...
  n) `..., x_1 ... x_{sizes[n-1]}  |- C #[x_1, ..., x_{sizes[n-1]}]`
  n+1) `..., (h_1 : a.size != sizes[0]), ..., (h_n : a.size != sizes[n-1]) |- C a`
  where `n = sizes.size` -/
def caseArraySizes (mvarId : MVarId) (fvarId : FVarId) (sizes : Array Nat) (xNamePrefix := `x) (hNamePrefix := `h) : MetaM (Array CaseArraySizesSubgoal) := do
let a := mkFVar fvarId;
α ← getArrayArgType a;
aSize ← mkAppM `Array.size #[a];
mvarId ← assertExt mvarId `aSize (mkConst `Nat) aSize;
(aSizeFVarId, mvarId) ← intro1 mvarId;
(hEq, mvarId) ← intro1 mvarId;
subgoals ← caseValues mvarId aSizeFVarId (sizes.map mkNatLit) hNamePrefix;
subgoals.mapIdxM fun i subgoal => do
  let subst  := subgoal.subst;
  let mvarId := subgoal.mvarId;
  let hEqSz  := (subst.get hEq).fvarId!;
  if h : i < sizes.size then do
     let n := sizes.get ⟨i, h⟩;
     mvarId ← clear mvarId (subgoal.newHs.get! 0);
     mvarId ← clear mvarId (subst.get aSizeFVarId).fvarId!;
     withMVarContext mvarId do
       hEqSzSymm ← mkEqSymm (mkFVar hEqSz);
       mvarId ← introArrayLit mvarId a n xNamePrefix hEqSzSymm;
       (xs, mvarId)  ← introN mvarId n;
       (hEqLit, mvarId) ← intro1 mvarId;
       mvarId ← clear mvarId hEqSz;
       (subst, mvarId) ← substCore mvarId hEqLit false subst;
       pure { mvarId := mvarId, elems := xs, subst := subst }
  else do
     (subst, mvarId) ← substCore mvarId hEq false subst;
     let diseqs := subgoal.newHs.map fun fvarId => (subst.get fvarId).fvarId!;
     pure { mvarId := mvarId, diseqs := diseqs, subst := subst }

end Meta
end Lean
