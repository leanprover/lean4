/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.FVarSubst

namespace Lean
namespace Meta

def substCore (mvarId : MVarId) (hFVarId : FVarId) (symm := false) (fvarSubst : FVarSubst := {}) (clearH := true) : MetaM (FVarSubst × MVarId) :=
withMVarContext mvarId $ do
  tag     ← getMVarTag mvarId;
  checkNotAssigned mvarId `subst;
  let hFVarIdOriginal := hFVarId;
  hLocalDecl ← getLocalDecl hFVarId;
  eq? ← matchEq? hLocalDecl.type;
  match eq? with
  | none => throwTacticEx `subst mvarId "argument must be an equality proof"
  | some (α, lhs, rhs) => do
    let a := if symm then rhs else lhs;
    let b := if symm then lhs else rhs;
    a ← whnf a;
    match a with
    | Expr.fvar aFVarId _ => do
      let aFVarIdOriginal := aFVarId;
      trace! `Meta.Tactic.subst ("substituting " ++ a ++ " (id: " ++ aFVarId ++ ") with " ++ b);
      mctx ← getMCtx;
      when (mctx.exprDependsOn b aFVarId) $
        throwTacticEx `subst mvarId ("'" ++ a ++ "' occurs at" ++ indentExpr b);
      aLocalDecl ← getLocalDecl aFVarId;
      (vars, mvarId) ← revert mvarId #[aFVarId, hFVarId] true;
      (twoVars, mvarId) ← introNP mvarId 2;
      trace! `Meta.Tactic.subst ("reverted variables " ++ toString vars);
      let aFVarId := twoVars.get! 0;
      let a       := mkFVar aFVarId;
      let hFVarId := twoVars.get! 1;
      let h       := mkFVar hFVarId;
      withMVarContext mvarId $ do
        mvarDecl   ← getMVarDecl mvarId;
        let type   := mvarDecl.type;
        hLocalDecl ← getLocalDecl hFVarId;
        eq? ← matchEq? hLocalDecl.type;
        match eq? with
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
            mvarId ←
              if clearH then do
                mvarId ← clear mvarId hFVarId;
                clear mvarId aFVarId
              else
                pure mvarId;
            (newFVars, mvarId) ← introNP mvarId (vars.size - 2);
            fvarSubst ← newFVars.size.foldM
              (fun i (fvarSubst : FVarSubst) =>
                let var     := vars.get! (i+2);
                let newFVar := newFVars.get! i;
                pure $ fvarSubst.insert var (mkFVar newFVar))
              fvarSubst;
            let fvarSubst := fvarSubst.insert aFVarIdOriginal (if clearH then b else mkFVar aFVarId);
            let fvarSubst := fvarSubst.insert hFVarIdOriginal (mkFVar hFVarId);
            pure (fvarSubst, mvarId)
          };
          if depElim then do
            let newType := type.replaceFVar a b;
            reflB ← mkEqRefl b;
            let newType := newType.replaceFVar h reflB;
            if symm then do
              motive ← mkLambdaFVars #[a, h] type;
              continue motive newType
            else do
              /- `type` depends on (h : a = b). So, we use the following trick to avoid a type incorrect motive.
                 1- Create a new local (hAux : b = a)
                 2- Create newType := type [hAux.symm / h]
                    `newType` is type correct because `h` and `hAux.symm` are definitionally equal by proof irrelevance.
                 3- Create motive by abstracting `a` and `hAux` in `newType`. -/
              hAuxType ← mkEq b a;
              motive ← withLocalDeclD `_h hAuxType $ fun hAux => do {
                hAuxSymm ← mkEqSymm hAux;
                /- replace h in type with hAuxSymm -/
                let newType := type.replaceFVar h hAuxSymm;
                mkLambdaFVars #[a, hAux] newType
              };
              continue motive newType
          else do
            motive ← mkLambdaFVars #[a] type;
            let newType := type.replaceFVar a b;
            continue motive newType
    | _ =>
      throwTacticEx `subst mvarId $
        "invalid equality proof, it is not of the form "
        ++ (if symm then "(t = x)" else "(x = t)")
        ++ indentExpr hLocalDecl.type
        ++ Format.line ++ "after WHNF, variable expected, but obtained" ++ indentExpr a

def subst (mvarId : MVarId) (hFVarId : FVarId) : MetaM MVarId :=
withMVarContext mvarId $ do
  hLocalDecl ← getLocalDecl hFVarId;
  eq? ← matchEq? hLocalDecl.type;
  match eq? with
  | some (α, lhs, rhs) => do
    rhs ← whnf rhs;
    if rhs.isFVar then
      Prod.snd <$> substCore mvarId hFVarId true
    else do
      lhs ← whnf lhs;
      if lhs.isFVar then
        Prod.snd <$> substCore mvarId hFVarId
      else do
        throwTacticEx `subst mvarId $
          "invalid equality proof, it is not of the form (x = t) or (t = x)"
          ++ indentExpr hLocalDecl.type
  | none => do
    mctx ← getMCtx;
    lctx ← getLCtx;
    some (fvarId, symm) ← lctx.findDeclM?
      (fun localDecl => if localDecl.isAuxDecl then pure none else do
       eq? ← matchEq? localDecl.type;
       match eq? with
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
