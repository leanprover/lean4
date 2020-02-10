/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

@[specialize]
def introNCoreAux {σ} (mvarId : MVarId) (mkName : LocalContext → Name → σ → Name × σ)
    : Nat → LocalContext → Array Expr → Nat → σ → Expr → MetaM (Array Expr × MVarId)
| 0, lctx, fvars, j, _, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
    withNewLocalInstances isClassExpensive fvars j $ do
      tag     ← getMVarTag mvarId;
      newMVar ← mkFreshExprSyntheticOpaqueMVar type tag;
      lctx    ← getLCtx;
      newVal  ← mkLambda fvars newMVar;
      assignExprMVar mvarId newVal;
      pure $ (fvars, newMVar.mvarId!)
| (i+1), lctx, fvars, j, s, Expr.letE n type val body _ => do
  let type   := type.instantiateRevRange j fvars.size fvars;
  let val    := val.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let (n, s) := mkName lctx n s;
  let lctx   := lctx.mkLetDecl fvarId n type val;
  let fvar   := mkFVar fvarId;
  let fvars  := fvars.push fvar;
  introNCoreAux i lctx fvars j s body
| (i+1), lctx, fvars, j, s, Expr.forallE n type body c => do
  let type   := type.instantiateRevRange j fvars.size fvars;
  fvarId ← mkFreshId;
  let (n, s) := mkName lctx n s;
  let lctx   := lctx.mkLocalDecl fvarId n type c.binderInfo;
  let fvar   := mkFVar fvarId;
  let fvars  := fvars.push fvar;
  introNCoreAux i lctx fvars j s body
| (i+1), lctx, fvars, j, s, type =>
  let type := type.instantiateRevRange j fvars.size fvars;
  adaptReader (fun (ctx : Context) => { lctx := lctx, .. ctx }) $
    withNewLocalInstances isClassExpensive fvars j $ do
      newType ← whnf type;
      if newType.isForall then
        introNCoreAux i lctx fvars fvars.size s newType
      else
        throwTacticEx `introN mvarId "insufficient number of binders"

@[specialize] def introNCore {σ} (mvarId : MVarId) (n : Nat) (mkName : LocalContext → Name → σ → Name × σ) (s : σ) : MetaM (Array FVarId × MVarId) :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `introN;
  mvarType ← getMVarType mvarId;
  lctx ← getLCtx;
  (fvars, mvarId) ← introNCoreAux mvarId mkName n lctx #[] 0 s mvarType;
  pure (fvars.map Expr.fvarId!, mvarId)

def mkAuxName (useUnusedNames : Bool) (lctx : LocalContext) (defaultName : Name) : List Name → Name × List Name
| []         => (if useUnusedNames then lctx.getUnusedName defaultName else defaultName, [])
| n :: rest  => (if n != "_" then n else if useUnusedNames then lctx.getUnusedName defaultName else defaultName, rest)

def introN (mvarId : MVarId) (n : Nat) (givenNames : List Name := []) (useUnusedNames := true) : MetaM (Array FVarId × MVarId) :=
introNCore mvarId n (mkAuxName useUnusedNames) givenNames

def intro (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
(fvarIds, mvarId) ← introN mvarId 1 [name];
pure (fvarIds.get! 0, mvarId)

def intro1 (mvarId : MVarId) : MetaM (FVarId × MVarId) := do
(fvarIds, mvarId) ← introN mvarId 1 [];
pure (fvarIds.get! 0, mvarId)

end Meta
end Lean
