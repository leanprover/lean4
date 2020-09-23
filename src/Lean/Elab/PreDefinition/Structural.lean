/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Meta.RecursorInfo
import Lean.Meta.Match.Match
import Lean.Elab.PreDefinition.Basic

namespace Lean
namespace Elab
open Meta

def registerStructualId : IO InternalExceptionId :=
registerInternalExceptionId `structuralRec
@[init registerStructualId]
constant structuralExceptionId : InternalExceptionId := arbitrary _

def throwStructuralFailed {α m} [MonadExceptOf Exception m] : m α :=
throw $ Exception.internal structuralExceptionId

private def getFixedPrefix (declName : Name) (xs : Array Expr) (value : Expr) : Nat :=
let visitor {ω} : StateRefT Nat (ST ω) Unit :=
  value.forEach' fun e =>
    if e.isAppOf declName then do
      let args := e.getAppArgs;
      modify fun numFixed => if args.size < numFixed then args.size else numFixed;
      -- we continue searching if the e's arguments are not a prefix of `xs`
      pure !args.isPrefixOf xs
    else
      pure true;
runST fun _ => do (_, numFixed) ← visitor.run xs.size; pure numFixed

structure RecArgInfo :=
/- `fixedParams ++ ys` are the arguments of the function we are trying to justify termination using structural recursion. -/
(fixedParams : Array Expr)
(ys          : Array Expr)  -- recursion arguments
(pos         : Nat)         -- position in `ys` of the argument we are recursing on
(indicesPos  : Array Nat)   -- position in `ys` of the inductive datatype indices we are recursing on
(indName     : Name)        -- inductive datatype name of the argument we are recursing on
(indLevels   : List Level)  -- inductice datatype universe levels of the argument we are recursing on
(indParams   : Array Expr)  -- inductive datatype parameters of the argument we are recursing on
(indIndices  : Array Expr)  -- inductive datatype indices of the argument we are recursing on, it is equal to `indicesPos.map fun i => ys.get! i`
(reflexive   : Bool)        -- true if we are recursing over a reflexive inductive datatype

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat :=
indices.foldl
  (fun minPos index => match xs.indexOf index with
    | some pos => if pos.val < minPos then pos.val else minPos
    | _        => minPos)
  xs.size

-- Indices can only depend on other indices
private def hasBadIndexDep? (ys : Array Expr) (indices : Array Expr) : MetaM (Option (Expr × Expr)) :=
indices.findSomeM? fun index => do
  indexType ← inferType index;
  ys.findSomeM? fun y =>
    if indices.contains y then pure none
    else condM (dependsOn indexType y.fvarId!)
      (pure (some (index, y)))
      (pure none)

-- Inductive datatype parameters cannot depend on ys
private def hasBadParamDep? (ys : Array Expr) (indParams : Array Expr) : MetaM (Option (Expr × Expr)) :=
indParams.findSomeM? fun p => do
  pType ← inferType p;
  ys.findSomeM? fun y =>
    condM (dependsOn pType y.fvarId!)
      (pure (some (p, y)))
      (pure none)

private partial def findRecArgAux {α} (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → MetaM α) : Nat → MetaM α
| i =>
  if h : i < xs.size then do
    let x := xs.get ⟨i, h⟩;
    localDecl ← getFVarLocalDecl x;
    if localDecl.isLet then
      throwStructuralFailed
    else do
      xType ← whnfD localDecl.type;
      matchConstInduct xType.getAppFn (fun _ => findRecArgAux (i+1)) fun indInfo us => do
      condM (not <$> hasConst (mkBRecOnFor indInfo.name)) (findRecArgAux (i+1)) do
      condM (do hasBInductionOn ← hasConst (mkBInductionOnFor indInfo.name); pure $ indInfo.isReflexive && !hasBInductionOn) (findRecArgAux (i+1)) do
        let indArgs    := xType.getAppArgs;
        let indParams  := indArgs.extract 0 indInfo.nparams;
        let indIndices := indArgs.extract indInfo.nparams indArgs.size;
        if !indIndices.all Expr.isFVar then do
          trace! `Elab.definition.structural
            ("argument #" ++ toString (i+1) ++ " was not used because its type is an inductive family and indices are not variables" ++ indentExpr xType);
          findRecArgAux (i+1)
        else if !indIndices.allDiff then do
          trace! `Elab.definition.structural
            ("argument #" ++ toString (i+1) ++ " was not used because its type is an inductive family and indices are not pairwise distinct" ++ indentExpr xType);
          findRecArgAux (i+1)
        else do
          let indexMinPos := getIndexMinPos xs indIndices;
          let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed;
          let fixedParams := xs.extract 0 numFixed;
          let ys          := xs.extract numFixed xs.size;
          badDep? ← hasBadIndexDep? ys indIndices;
          match badDep? with
          | some (index, y) => do
            trace! `Elab.definition.structural
              ("argument #" ++ toString (i+1) ++ " was not used because its type is an inductive family" ++ indentExpr xType ++
               Format.line ++ "and index" ++ indentExpr index ++
               Format.line ++ "depends on the non index" ++ indentExpr y);
            findRecArgAux (i+1)
          | none => do
            badDep? ← hasBadParamDep? ys indParams;
            match badDep? with
            | some (indParam, y) => do
              trace! `Elab.definition.structural
                ("argument #" ++ toString (i+1) ++ " was not used because its type is an inductive datatype" ++ indentExpr xType ++
                 Format.line ++ "and parameter" ++ indentExpr indParam ++
                 Format.line ++ "depends on" ++ indentExpr y);
              findRecArgAux (i+1)
            | none => do
              let indicesPos := indIndices.map fun index => match ys.indexOf index with | some i => i.val | none => unreachable!;
              catchInternalId structuralExceptionId
                (k { fixedParams := fixedParams, ys := ys, pos := i - fixedParams.size,
                     indicesPos  := indicesPos,
                     indName     := indInfo.name,
                     indLevels   := us,
                     indParams   := indParams,
                     indIndices  := indIndices,
                     reflexive := indInfo.isReflexive })
                (fun _ => findRecArgAux (i+1))
  else
    throwStructuralFailed

@[inline] private def findRecArg {α} (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → MetaM α) : MetaM α :=
findRecArgAux numFixed xs k numFixed

private partial def replaceRecApps (argInfo : RecArgInfo) (major : Expr) (below : Expr) : Expr → MetaM Expr
| e@(Expr.lam _ _ _ _) => lambdaTelescope e fun xs b => do b ← replaceRecApps b; mkLambdaFVars xs b
| Expr.letE n type val body _ => do
  val ← replaceRecApps val;
  withLetDecl n type val fun x => do
    body ← replaceRecApps body;
    mkLetFVars #[x] body
| Expr.mdata d e _   => do e ← replaceRecApps e; pure $ mkMData d e
| Expr.proj n i e _  => do e ← replaceRecApps e; pure $ mkProj n i e
| e@(Expr.app _ _ _) => do
  let processApp (e : Expr) : MetaM Expr :=
    e.withApp fun f args => do {
      f ← replaceRecApps f;
      args ← args.mapM replaceRecApps;
      pure $ mkAppN f args
    };
  matcherApp? ← matchMatcherApp? e;
  match matcherApp? with
  | some matcherApp =>
    if matcherApp.discrs.contains major then do
      trace! `Elab.definition.structural ("found matcher");
      matcherApp ← matcherApp.addArg below;
      -- TODO
      pure matcherApp.toExpr
    else
      processApp e
  | none => processApp e
| e => pure e

private def mkBRecOn (argInfo : RecArgInfo) (value : Expr) : MetaM Expr := do
type ← inferType value;
let type := type.headBeta;
let major := argInfo.ys.get! argInfo.pos;
let otherArgs := argInfo.ys.filter fun y => y != major && !argInfo.indIndices.contains y;
motive ← mkForallFVars otherArgs type;
brecOnUniv ← getLevel motive;
motive ← mkLambdaFVars (argInfo.indIndices.push major) motive;
trace! `Elab.definition.structural ("brecOn motive: " ++ motive);
let brecOn := Lean.mkConst (mkBRecOnFor argInfo.indName) (brecOnUniv :: argInfo.indLevels);
let brecOn := mkAppN brecOn argInfo.indParams;
let brecOn := mkApp brecOn motive;
let brecOn := mkAppN brecOn argInfo.indIndices;
let brecOn := mkApp brecOn major;
brecOnType ← inferType brecOn;
trace! `Elab.definition.structural ("brecOn     " ++ brecOn);
trace! `Elab.definition.structural ("brecOnType " ++ brecOnType);
forallBoundedTelescope brecOnType (some 1) fun F _ => do
  let F := F.get! 0;
  FType ← inferType F;
  let numIndices := argInfo.indIndices.size;
  forallBoundedTelescope FType (some $ numIndices + 1 /- major -/ + 1 /- below -/ + otherArgs.size) fun Fargs _ => do
    let indicesNew   := Fargs.extract 0 numIndices;
    let majorNew     := Fargs.get! numIndices;
    let below        := Fargs.get! (numIndices+1);
    let otherArgsNew := Fargs.extract (numIndices+2) Fargs.size;
    let valueNew     := value.replaceFVars argInfo.indIndices indicesNew;
    let valueNew     := valueNew.replaceFVar major majorNew;
    let valueNew     := valueNew.replaceFVars otherArgs otherArgsNew;
    valueNew ← replaceRecApps argInfo majorNew below valueNew;
    Farg ← mkLambdaFVars Fargs valueNew;
    let brecOn := mkApp brecOn Farg;
    pure $ mkAppN brecOn otherArgs

private def elimRecursion (preDef : PreDefinition) : MetaM PreDefinition :=
lambdaTelescope preDef.value fun xs value => do
  trace! `Elab.definition.structural (preDef.declName ++ " " ++ xs ++ " :=\n" ++ value);
  let numFixed := getFixedPrefix preDef.declName xs value;
  findRecArg numFixed xs fun argInfo => do
    -- when (argInfo.indName == `Nat) throwStructuralFailed; -- HACK to skip Nat argument
    valueNew ← mkBRecOn argInfo value;
    valueNew ← mkLambdaFVars xs valueNew;
    trace! `Elab.definition.structural ("result: " ++ valueNew);
    -- pure $ some { preDef with value := valueNew }
    throwError "WIP"

def structuralRecursion (preDefs : Array PreDefinition) : TermElabM Bool :=
if preDefs.size != 1 then
  pure false
else
  catchInternalId structuralExceptionId
    (do preDefNonRec ← liftMetaM $ elimRecursion (preDefs.get! 0);
        addNonRec preDefNonRec;
        addAndCompileUnsafeRec preDefs;
        pure true)
    (fun _ => pure false)

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.definition.structural;
pure ()

end Elab
end Lean
