/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.AppBuilder
import Init.Lean.Meta.Message
import Init.Lean.Meta.Tactic.Util
import Init.Lean.Meta.Tactic.Revert
import Init.Lean.Meta.Tactic.Intro
import Init.Lean.Meta.Tactic.Clear
import Init.Lean.Meta.Tactic.FVarSubst

namespace Lean
namespace Meta

def substCore (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (genFVarSubst := false) : MetaM (FVarSubst × MVarId) :=
withMVarContext mvarId $ do
  tag     ← getMVarTag mvarId;
  checkNotAssigned mvarId `subst;
  hLocalDecl ← getLocalDecl hFVarId;
  match hLocalDecl.type.eq? with
  | none => throwTacticEx `subst mvarId "argument must be an equality proof"
  | some (α, lhs, rhs) =>
    let a := if symm then rhs else lhs;
    let b := if symm then lhs else rhs;
    match a with
    | Expr.fvar aFVarId _ => do
      mctx ← getMCtx;
      when (mctx.exprDependsOn b aFVarId) $
        throwTacticEx `subst mvarId ("'" ++ a ++ "' occurs at" ++ indentExpr b);
      aLocalDecl ← getLocalDecl aFVarId;
      (vars, mvarId) ← revert mvarId #[aFVarId, hFVarId] true;
      (twoVars, mvarId) ← introN mvarId 2 [] false;
      let aFVarId := twoVars.get! 0;
      let a       := mkFVar aFVarId;
      let hFVarId := twoVars.get! 1;
      let h       := mkFVar hFVarId;
      withMVarContext mvarId $ do
        mvarDecl   ← getMVarDecl mvarId;
        let type   := mvarDecl.type;
        hLocalDecl ← getLocalDecl hFVarId;
        match hLocalDecl.type.eq? with
        | none => unreachable!
        | some (α, lhs, rhs) => do
          let b       := if symm then lhs else rhs;
          mctx        ← getMCtx;
          let depElim := mctx.exprDependsOn mvarDecl.type hFVarId;
          let continue (motive : Expr) (newType : Expr) : MetaM (FVarSubst × MVarId) := do {
            major   ← if symm then pure h else mkEqSymm h;
            newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag;
            let minor := newMVar;
            newVal  ← if depElim then mkEqRec motive minor major else mkEqNDRec motive minor major;
            assignExprMVar mvarId newVal;
            let mvarId := newMVar.mvarId!;
            mvarId ← clear mvarId hFVarId;
            mvarId ← clear mvarId aFVarId;
            (newFVars, mvarId) ← introN mvarId (vars.size - 2) [] false;
            fvarSubst ← newFVars.size.foldM
              (fun i (fvarSubst : FVarSubst) =>
                let var      := vars.get! i;
                let newFVar := newFVars.get! i;
                pure $ fvarSubst.insert var (mkFVar newFVar))
              FVarSubst.empty;
            pure (fvarSubst, mvarId)
          };
          if depElim then do
            let newType := (type.abstract #[a]).instantiate1 b;
            reflB ← mkEqRefl b;
            let newType := (newType.abstract #[h]).instantiate1 reflB;
            if symm then do
              motive ← mkLambda #[a, h] type;
              continue motive newType
            else do
              /- `type` depends on (h : a = b). So, we use the following trick to avoid a type incorrect motive.
                 1- Create a new local (hAux : b = a)
                 2- Create newType := type [hAux.symm / h]
                    `newType` is type correct because `h` and `hAux.symm` are definitionally equal by proof irrelevance.
                 3- Create motive by abstracting `a` and `hAux` in `newType`. -/
              hAuxType ← mkEq b a;
              motive ← withLocalDecl `_h hAuxType BinderInfo.default $ fun hAux => do {
                hAuxSymm ← mkEqSymm hAux;
                /- replace h in type with hAuxSymm -/
                let newType := (type.abstract #[h]).instantiate1 hAuxSymm;
                mkLambda #[a, hAux] newType
              };
              continue motive newType
          else do
            motive ← mkLambda #[a] type;
            let newType := (type.abstract #[a]).instantiate1 b;
            continue motive newType
    | _ =>
      throwTacticEx `subst mvarId $
        "invalid equality proof, it is not of the form "
        ++ (if symm then "(t = x)" else "(x = t)")
        ++ indentExpr hLocalDecl.type

def subst (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId :=
withMVarContext mvarId $ do
  hLocalDecl ← getLocalDecl hFVarId;
  match hLocalDecl.type.eq? with
  | some (α, lhs, rhs) =>
    if rhs.isFVar then
      Prod.snd <$> substCore mvarId hFVarId true
    else if lhs.isFVar then
      Prod.snd <$> substCore mvarId hFVarId
    else
      throwTacticEx `subst mvarId $
        "invalid equality proof, it is not of the form (x = t) or (t = x)"
        ++ indentExpr hLocalDecl.type
  | none => do
    mctx ← getMCtx;
    lctx ← getLCtx;
    some (fvarId, symm) ← lctx.findDeclM?
      (fun localDecl => match localDecl.type.eq? with
       | some (α, lhs, rhs) =>
         if rhs.isFVar && rhs.fvarId! == hFVarId && !mctx.exprDependsOn lhs hFVarId then
           pure $ some (localDecl.fvarId, true)
         else if lhs.isFVar && lhs.fvarId! == hFVarId && !mctx.exprDependsOn rhs hFVarId then
           pure $ some (localDecl.fvarId, false)
         else
           pure none
       | _ => pure none)
      | throwTacticEx `subst mvarId ("did not find equation for eliminating '" ++ mkFVar hFVarId ++ "'");
    Prod.snd <$> substCore mvarId fvarId symm

@[init] private def regTraceClasses : IO Unit :=
registerTraceClass `Meta.Tactic.subst

end Meta
end Lean
