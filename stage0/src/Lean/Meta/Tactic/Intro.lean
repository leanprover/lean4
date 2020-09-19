/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

@[specialize]
private partial def introNImpAux {σ} (mvarId : MVarId) (mkName : LocalContext → Name → σ → MetaM (Name × σ))
    : Nat → LocalContext → Array Expr → Nat → σ → Expr → MetaM (Array Expr × MVarId)
| 0, lctx, fvars, j, _, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstances fvars j $ do
      tag     ← getMVarTag mvarId;
      let type := type.headBeta;
      newMVar ← mkFreshExprSyntheticOpaqueMVar type tag;
      lctx    ← getLCtx;
      newVal  ← mkLambdaFVars fvars newMVar;
      assignExprMVar mvarId newVal;
      pure $ (fvars, newMVar.mvarId!)
| (i+1), lctx, fvars, j, s, Expr.letE n type val body _ => do
  let type   := type.instantiateRevRange j fvars.size fvars;
  let type   := type.headBeta;
  let val    := val.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  (n, s) ← mkName lctx n s;
  let lctx   := lctx.mkLetDecl fvarId n type val;
  let fvar   := mkFVar fvarId;
  let fvars  := fvars.push fvar;
  introNImpAux i lctx fvars j s body
| (i+1), lctx, fvars, j, s, Expr.forallE n type body c => do
  let type   := type.instantiateRevRange j fvars.size fvars;
  let type   := type.headBeta;
  fvarId ← mkFreshId;
  (n, s) ← mkName lctx n s;
  let lctx   := lctx.mkLocalDecl fvarId n type c.binderInfo;
  let fvar   := mkFVar fvarId;
  let fvars  := fvars.push fvar;
  introNImpAux i lctx fvars j s body
| (i+1), lctx, fvars, j, s, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { ctx with lctx := lctx }) $
    withNewLocalInstances fvars j $ do
      newType ← whnf type;
      if newType.isForall then
        introNImpAux (i+1) lctx fvars fvars.size s newType
      else
        throwTacticEx `introN mvarId "insufficient number of binders"

@[specialize] private def introNImp {σ} (mvarId : MVarId) (n : Nat) (mkName : LocalContext → Name → σ → MetaM (Name × σ)) (s : σ) : MetaM (Array FVarId × MVarId) :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `introN;
  mvarType ← getMVarType mvarId;
  lctx ← getLCtx;
  (fvars, mvarId) ← introNImpAux mvarId mkName n lctx #[] 0 s mvarType;
  pure (fvars.map Expr.fvarId!, mvarId)

def hygienicIntroDef := true

def getHygienicIntro : MetaM Bool := do
o ← getOptions;
pure $ o.get `hygienicIntro hygienicIntroDef

@[init] def registerHygienicIntro : IO Unit :=
registerOption `hygienicIntro { defValue := hygienicIntroDef, group := "tactic", descr := "make sure 'intro'-like tactics are hygienic" }

private def mkAuxNameImp (preserveBinderNames : Bool) (hygienic : Bool) (lctx : LocalContext) (binderName : Name) : List Name → MetaM (Name × List Name)
| []         =>
  if preserveBinderNames then
    pure (binderName, [])
  else if hygienic then do
    binderName ← Core.mkFreshUserName binderName;
    pure (binderName, [])
  else
    pure (lctx.getUnusedName binderName, [])
| n :: rest  =>
  if n != "_" then pure (n, rest)
  else if preserveBinderNames then
    pure (binderName, rest)
  else if hygienic then do
    binderName ← Core.mkFreshUserName binderName;
    pure (binderName, rest)
  else
    pure (lctx.getUnusedName binderName, rest)

def introNCore (mvarId : MVarId) (n : Nat) (givenNames : List Name) (preserveBinderNames : Bool) : MetaM (Array FVarId × MVarId) := do
hygienic ← getHygienicIntro;
if n == 0 then pure (#[], mvarId)
else introNImp mvarId n (mkAuxNameImp preserveBinderNames hygienic) givenNames

abbrev introN (mvarId : MVarId) (n : Nat) (givenNames : List Name := []) : MetaM (Array FVarId × MVarId) :=
introNCore mvarId n givenNames false

abbrev introNP (mvarId : MVarId) (n : Nat) : MetaM (Array FVarId × MVarId) :=
introNCore mvarId n [] true

def intro (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
(fvarIds, mvarId) ← introN mvarId 1 [name];
pure (fvarIds.get! 0, mvarId)

def intro1Core (mvarId : MVarId) (preserveBinderNames : Bool) : MetaM (FVarId × MVarId) := do
(fvarIds, mvarId) ← introNCore mvarId 1 [] preserveBinderNames;
pure (fvarIds.get! 0, mvarId)

abbrev intro1 (mvarId : MVarId) : MetaM (FVarId × MVarId) := do
intro1Core mvarId false

abbrev intro1P (mvarId : MVarId) : MetaM (FVarId × MVarId) := do
intro1Core mvarId true

end Meta
end Lean
