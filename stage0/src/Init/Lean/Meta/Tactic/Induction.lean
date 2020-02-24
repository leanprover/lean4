/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.RecursorInfo
import Init.Lean.Meta.SynthInstance
import Init.Lean.Meta.Tactic.Util
import Init.Lean.Meta.Tactic.Revert
import Init.Lean.Meta.Tactic.Intro
import Init.Lean.Meta.Tactic.Clear
import Init.Lean.Meta.Tactic.FVarSubst

namespace Lean
namespace Meta

private partial def getTargetArity : Expr → Nat
| Expr.mdata _ b _     => getTargetArity b
| Expr.forallE _ _ b _ => getTargetArity b + 1
| e                    => if e.isHeadBetaTarget then getTargetArity e.headBeta else 0

private def addRecParams (mvarId : MVarId) (majorTypeArgs : Array Expr) : List (Option Nat) → Expr → MetaM Expr
| [], rec => pure rec
| some pos :: rest, rec =>
  if h : pos < majorTypeArgs.size then
    addRecParams rest (mkApp rec (majorTypeArgs.get ⟨pos, h⟩))
  else
    throwTacticEx `induction mvarId ("ill-formed recursor")
| none :: rest, rec => do
  recType ← inferType rec;
  recType ← whnfForall recType;
  match recType with
  | Expr.forallE _ d _ _ => do
    param ← catch (synthInstance d) (fun _ => throwTacticEx `induction mvarId "failed to generate type class instance parameter");
    addRecParams rest (mkApp rec param)
  | _ =>
    throwTacticEx `induction mvarId ("ill-formed recursor")

structure InductionSubgoal :=
(mvarId : MVarId)
(fields : Array FVarId := #[])
(subst  : FVarSubst := {})

instance InductionSubgoal.inhabited : Inhabited InductionSubgoal := ⟨{ mvarId := arbitrary _ }⟩

private def getTypeBody (mvarId : MVarId) (type : Expr) (x : Expr) : MetaM Expr := do
type ← whnfForall type;
match type with
| Expr.forallE _ _ b _ => pure $ b.instantiate1 x
| _                    => throwTacticEx `induction mvarId "ill-formed recursor"

private partial def finalizeAux
    (mvarId : MVarId) (givenNames : Array (List Name)) (recInfo : RecursorInfo)
    (reverted : Array FVarId) (major : Expr) (initialArity : Nat) (indices : Array Expr) (numMinors : Nat) (baseSubst : FVarSubst)
    : Nat → Nat → Expr → Expr → Bool → Array InductionSubgoal → MetaM (Array InductionSubgoal)
| pos, minorIdx, rec, recType, consumedMajor, subgoals => do
  recType ← whnfForall recType;
  if recType.isForall && pos < recInfo.numArgs then
    if pos == recInfo.firstIndexPos then do
      (rec, recType) ← indices.foldlM
        (fun (acc : Expr × Expr) (index : Expr) => do
          let (rec, recType) := acc;
          let rec := mkApp rec index;
          recType ← getTypeBody mvarId recType index;
          pure (rec, recType))
        (rec, recType);
      let rec := mkApp rec major;
      recType ← getTypeBody mvarId recType major;
      finalizeAux (pos+1+indices.size) minorIdx rec recType true subgoals
    else do
      -- consume motive
      tag ← getMVarTag mvarId;
      when (minorIdx ≥ numMinors) $ throwTacticEx `induction mvarId "ill-formed recursor";
      match recType with
      | Expr.forallE n d b c =>
        let d := d.headBeta;
        -- Remark is givenNames is not empty, then user provided explicit alternatives for each minor premise
        if c.binderInfo.isInstImplicit && givenNames.isEmpty then do
          inst? ← synthInstance? d;
          match inst? with
          | some inst => do
            let rec := mkApp rec inst;
            recType ← getTypeBody mvarId recType inst;
            finalizeAux (pos+1) (minorIdx+1) rec recType consumedMajor subgoals
          | none => do
            -- Add newSubgoal if type class resolution failed
            mvar ← mkFreshExprSyntheticOpaqueMVar d (tag ++ n);
            let rec := mkApp rec mvar;
            recType ← getTypeBody mvarId recType mvar;
            finalizeAux (pos+1) (minorIdx+1) rec recType consumedMajor (subgoals.push { mvarId := mvar.mvarId! })
        else do
          let arity := getTargetArity d;
          when (arity < initialArity) $ throwTacticEx `induction mvarId "ill-formed recursor";
          let nparams := arity - initialArity; -- number of fields due to minor premise
          let nextra  := reverted.size - indices.size - 1; -- extra dependencies that have been reverted
          let minorGivenNames := if h : minorIdx < givenNames.size then givenNames.get ⟨minorIdx, h⟩ else [];
          mvar ← mkFreshExprSyntheticOpaqueMVar d (tag ++ n);
          let rec := mkApp rec mvar;
          recType ← getTypeBody mvarId recType mvar;
          -- Try to clear major premise from new goal
          mvarId' ← tryClear mvar.mvarId! major.fvarId!;
          (fields, mvarId') ← introN mvarId' nparams minorGivenNames true;
          (extra,  mvarId') ← introN mvarId' nextra [] false;
          let subst := reverted.size.fold
            (fun i (subst : FVarSubst) =>
              if i ≤ indices.size + 1 then subst
              else
                let revertedFVarId := reverted.get! i;
                let newFVarId      := extra.get! (i - indices.size - 1);
                subst.insert revertedFVarId (mkFVar newFVarId))
            baseSubst;
          finalizeAux (pos+1) (minorIdx+1) rec recType consumedMajor (subgoals.push { mvarId := mvarId', fields := fields, subst := subst })
      | _ => unreachable!
  else do
    unless consumedMajor $ throwTacticEx `induction mvarId "ill-formed recursor";
    assignExprMVar mvarId rec;
    pure subgoals

private def finalize
    (mvarId : MVarId) (givenNames : Array (List Name)) (recInfo : RecursorInfo)
    (reverted : Array FVarId) (major : Expr) (indices : Array Expr) (baseSubst : FVarSubst) (rec : Expr)
    : MetaM (Array InductionSubgoal) := do
target ← getMVarType mvarId;
let initialArity := getTargetArity target;
recType ← inferType rec;
let numMinors := recInfo.produceMotive.length;
finalizeAux mvarId givenNames recInfo reverted major initialArity indices numMinors baseSubst (recInfo.paramsPos.length + 1) 0 rec recType false #[]

def induction (mvarId : MVarId) (majorFVarId : FVarId) (recName : Name) (givenNames : Array (List Name) := #[]) (useUnusedNames := false) :
    MetaM (Array InductionSubgoal) :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `induction;
  majorLocalDecl ← getLocalDecl majorFVarId;
  recInfo ← mkRecursorInfo recName;
  majorType ← whnfUntil majorLocalDecl.type recInfo.typeName;
  majorType.withApp $ fun _ majorTypeArgs => do
    recInfo.paramsPos.forM $ fun paramPos? => do {
      match paramPos? with
      | none          => pure ()
      | some paramPos => when (paramPos ≥ majorTypeArgs.size) $ throwTacticEx `induction mvarId ("major premise type is ill-formed" ++ indentExpr majorType)
    };
    mctx ← getMCtx;
    indices ← recInfo.indicesPos.toArray.mapM $ fun idxPos => do {
      when (idxPos ≥ majorTypeArgs.size) $ throwTacticEx `induction mvarId ("major premise type is ill-formed" ++ indentExpr majorType);
      let idx := majorTypeArgs.get! idxPos;
      unless idx.isFVar $ throwTacticEx `induction mvarId ("major premise type index " ++ idx ++ " is not variable " ++ indentExpr majorType);
      majorTypeArgs.size.forM $ fun i => do {
        let arg := majorTypeArgs.get! i;
        when (i != idxPos && arg == idx) $
          throwTacticEx `induction mvarId ("'" ++ idx ++ "' is an index in major premise, but it occurs more than once" ++ indentExpr majorType);
        when (i < idxPos && mctx.exprDependsOn arg idx.fvarId!) $
          throwTacticEx `induction mvarId ("'" ++ idx ++ "' is an index in major premise, but it occurs in previous arguments" ++ indentExpr majorType);
        -- If arg is also and index and a variable occurring after `idx`, we need to make sure it doesn't depend on `idx`.
        -- Note that if `arg` is not a variable, we will fail anyway when we visit it.
        when (i > idxPos && recInfo.indicesPos.contains i && arg.isFVar) $ do {
          idxDecl ← getLocalDecl idx.fvarId!;
          when (mctx.localDeclDependsOn idxDecl arg.fvarId!) $
            throwTacticEx `induction mvarId ("'" ++ idx ++ "' is an index in major premise, but it depends on index occurring at position #" ++ toString (i+1))
        }
      };
      pure idx
    };
    target ← getMVarType mvarId;
    when (!recInfo.depElim && mctx.exprDependsOn target majorFVarId) $
      throwTacticEx `induction mvarId ("recursor '" ++ recName ++ "' does not support dependent elimination, but conclusion depends on major premise");
    -- Revert indices and major premise preserving variable order
    (reverted, mvarId) ← revert mvarId ((indices.map Expr.fvarId!).push majorFVarId) true;
    -- Re-introduce indices and major
    (indices', mvarId) ← introN mvarId indices.size [] false;
    (majorFVarId', mvarId) ← intro1 mvarId false;
    -- Create FVarSubst with indices
    let baseSubst : FVarSubst := indices.iterate {} (fun i index subst => subst.insert index.fvarId! (mkFVar (indices'.get! i.val)));
    -- Update indices and major
    let indices := indices'.map mkFVar;
    let majorFVarId := majorFVarId';
    let major := mkFVar majorFVarId;
    withMVarContext mvarId $ do
      target ← getMVarType mvarId;
      targetLevel ← getLevel target;
      majorLocalDecl ← getLocalDecl majorFVarId;
      majorType ← whnfUntil majorLocalDecl.type recInfo.typeName;
      majorType.withApp $ fun majorTypeFn majorTypeArgs => do
        match majorTypeFn with
        | Expr.const majorTypeFnName majorTypeFnLevels _ => do
          let majorTypeFnLevels := majorTypeFnLevels.toArray;
          (recLevels, foundTargetLevel) ← recInfo.univLevelPos.foldlM
            (fun (result : Array Level × Bool) (univPos : RecursorUnivLevelPos) =>
              let (recLevels, foundTargetLevel) := result;
              match univPos with
              | RecursorUnivLevelPos.motive => pure (recLevels.push targetLevel, true)
              | RecursorUnivLevelPos.majorType idx => do
                when (idx ≥ majorTypeFnLevels.size) $
                  throwTacticEx `induction mvarId ("ill-formed recursor");
                pure (recLevels.push (majorTypeFnLevels.get! idx), foundTargetLevel))
            (#[], false);
          when (!foundTargetLevel && !targetLevel.isZero) $
            throwTacticEx `induction mvarId ("recursor '" ++ recName ++ "' can only eliminate into Prop");
          let rec := mkConst recName recLevels.toList;
          rec ← addRecParams mvarId majorTypeArgs recInfo.paramsPos rec;
          -- Compute motive
          let motive := target;
          motive ← if recInfo.depElim then mkLambda #[major] motive else pure motive;
          motive ← mkLambda indices motive;
          let rec := mkApp rec motive;
          finalize mvarId givenNames recInfo reverted major indices baseSubst rec
        | _ =>
         throwTacticEx `induction mvarId "major premise is not of the form (C ...)"

end Meta
end Lean
