/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Meta.ForEachExpr
import Lean.Meta.RecursorInfo
import Lean.Meta.Match.Match
import Lean.Elab.PreDefinition.Basic

namespace Lean
namespace Elab
open Meta

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
  (fun minPos index => match xs.indexOf? index with
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

private def throwStructuralFailed {α} : MetaM α :=
throwError "structural recursion cannot be used"

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
        if !indIndices.all Expr.isFVar then
          orelseMergeErrors
            (throwError $ "argument #" ++ toString (i+1) ++ " was not used because its type is an inductive family and indices are not variables" ++ indentExpr xType)
            (findRecArgAux (i+1))
        else if !indIndices.allDiff then
          orelseMergeErrors
            (throwError $ "argument #" ++ toString (i+1)
              ++ " was not used because its type is an inductive family and indices are not pairwise distinct" ++ indentExpr xType)
            (findRecArgAux (i+1))
        else do
          let indexMinPos := getIndexMinPos xs indIndices;
          let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed;
          let fixedParams := xs.extract 0 numFixed;
          let ys          := xs.extract numFixed xs.size;
          badDep? ← hasBadIndexDep? ys indIndices;
          match badDep? with
          | some (index, y) =>
            orelseMergeErrors
              (throwError $
                "argument #" ++ toString (i+1) ++ " was not used because its type is an inductive family" ++ indentExpr xType ++
                Format.line ++ "and index" ++ indentExpr index ++
                Format.line ++ "depends on the non index" ++ indentExpr y)
              (findRecArgAux (i+1))
          | none => do
            badDep? ← hasBadParamDep? ys indParams;
            match badDep? with
            | some (indParam, y) =>
              orelseMergeErrors
                (throwError $
                  "argument #" ++ toString (i+1) ++ " was not used because its type is an inductive datatype" ++ indentExpr xType ++
                  Format.line ++ "and parameter" ++ indentExpr indParam ++
                  Format.line ++ "depends on" ++ indentExpr y)
                (findRecArgAux (i+1))
            | none => do
              let indicesPos := indIndices.map fun index => match ys.indexOf? index with | some i => i.val | none => unreachable!;
              orelseMergeErrors
                (k { fixedParams := fixedParams, ys := ys, pos := i - fixedParams.size,
                     indicesPos  := indicesPos,
                     indName     := indInfo.name,
                     indLevels   := us,
                     indParams   := indParams,
                     indIndices  := indIndices,
                     reflexive := indInfo.isReflexive })
                (findRecArgAux (i+1))
  else
    throwStructuralFailed

@[inline] private def findRecArg {α} (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → MetaM α) : MetaM α :=
findRecArgAux numFixed xs k numFixed

private def containsRecFn (recFnName : Name) (e : Expr) : Bool :=
(e.find? fun e => e.isConstOf recFnName).isSome

private def ensureNoRecFn (recFnName : Name) (e : Expr) : MetaM Expr := do
if containsRecFn recFnName e then do
  Meta.forEachExpr e fun e => when (e.isAppOf recFnName) $
    throwError $ "unexpected occurrence of recursive application" ++ indentExpr e;
  pure e
else
  pure e

private def throwToBelowFailed {α} : MetaM α :=
throwError "toBelow failed"

/- See toBelow -/
private partial def toBelowAux (C : Expr) : Expr → Expr → Expr → MetaM Expr
| belowDict, arg, F => do
  belowDict ← whnf belowDict;
  trace! `Elab.definition.structural ("belowDict: " ++ belowDict ++ ", arg: " ++ arg);
  match belowDict with
  | Expr.app (Expr.app (Expr.const `PProd _ _) d1 _) d2 _ =>
    (do F ← mkAppM `PProd.fst #[F]; toBelowAux d1 arg F)
    <|>
    (do F ← mkAppM `PProd.snd #[F]; toBelowAux d2 arg F)
  | Expr.app (Expr.app (Expr.const `And _ _) d1 _) d2 _ =>
    (do F ← mkAppM `And.left #[F]; toBelowAux d1 arg F)
    <|>
    (do F ← mkAppM `And.right #[F]; toBelowAux d2 arg F)
  | _ => forallTelescopeReducing belowDict fun xs belowDict => do
    let argArgs := arg.getAppArgs;
    unless (argArgs.size >= xs.size) throwToBelowFailed;
    let n := argArgs.size;
    let argTailArgs := argArgs.extract (n - xs.size) n;
    let belowDict := belowDict.replaceFVars xs argTailArgs;
    match belowDict with
    | Expr.app belowDictFun belowDictArg _ => do
      unless (belowDictFun.getAppFn == C) throwToBelowFailed;
      unlessM (isDefEq belowDictArg arg) throwToBelowFailed;
      pure (mkAppN F argTailArgs)
    | _ => throwToBelowFailed

/- See toBelow -/
private def withBelowDict {α} (below : Expr) (numIndParams : Nat) (k : Expr → Expr → MetaM α) : MetaM α := do
belowType ← inferType below;
trace! `Elab.definition.structural ("belowType: " ++ belowType);
belowType.withApp fun f args => do
  let motivePos := numIndParams + 1;
  unless (motivePos < args.size) $ throwError $ "unexpected 'below' type" ++ indentExpr belowType;
  let pre := mkAppN f (args.extract 0 numIndParams);
  preType ← inferType pre;
  forallBoundedTelescope preType (some 1) fun x _ => do
    motiveType ← inferType (x.get! 0);
    C ← Core.mkFreshUserName `C;
    withLocalDeclD C motiveType fun C =>
      let belowDict := mkApp pre C;
      let belowDict := mkAppN belowDict (args.extract (numIndParams + 1) args.size);
      k C belowDict

/-
  `below` is a free variable with type of the form `I.below indParams motive indices major`,
  where `I` is the name of an inductive datatype.

  For example, when trying to show that the following function terminates using structural recursion
  ```lean
  def addAdjacent : List Nat → List Nat
  | []       => []
  | [a]      => [a]
  | a::b::as => (a+b) :: addAdjacent as
  ```
  when we are visiting `addAdjacent as` at `replaceRecApps`, `below` has type
  `@List.below Nat (fun (x : List Nat) => List Nat) (a::b::as)`
  The motive `fun (x : List Nat) => List Nat` depends on the actual function we are trying to compute.
  So, we first replace it with a fresh variable `C` at `withBelowDict`.
  Recall that `brecOn` implements course-of-values recursion, and `below` can be viewed as a dictionary
  of the "previous values".
  We search this dictionary using the auxiliary function `toBelowAux`.
  The dictionary is built using the `PProd` (`And` for inductive predicates).
  We keep searching it until we find `C recArg`, where `C` is the auxiliary fresh variable created at `withBelowDict`.  -/
private partial def toBelow (below : Expr) (numIndParams : Nat) (recArg : Expr) : MetaM Expr := do
withBelowDict below numIndParams fun C belowDict =>
  toBelowAux C belowDict recArg below

private partial def replaceRecApps (recFnName : Name) (recArgInfo : RecArgInfo) : Expr → Expr → MetaM Expr
| below, e@(Expr.lam n d b c) => do
  d ← replaceRecApps below d;
  withLocalDecl n c.binderInfo d fun x => do
    b ← replaceRecApps below (b.instantiate1 x);
    mkLambdaFVars #[x] b
| below, e@(Expr.forallE n d b c) => do
  d ← replaceRecApps below d;
  withLocalDecl n c.binderInfo d fun x => do
    b ← replaceRecApps below (b.instantiate1 x);
    mkForallFVars #[x] b
| below, Expr.letE n type val body _ => do
  type ← replaceRecApps below type;
  val  ← replaceRecApps below val;
  withLetDecl n type val fun x => do
    body ← replaceRecApps below (body.instantiate1 x);
    mkLetFVars #[x] body
| below, Expr.mdata d e _   => do e ← replaceRecApps below e; pure $ mkMData d e
| below, Expr.proj n i e _  => do e ← replaceRecApps below e; pure $ mkProj n i e
| below, e@(Expr.app _ _ _) => do
  let processApp (e : Expr) : MetaM Expr :=
    e.withApp fun f args => do {
      if f.isConstOf recFnName then do
        let numFixed  := recArgInfo.fixedParams.size;
        let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos;
        when (recArgPos >= args.size) $ throwError ("insufficient number of parameters at recursive application " ++ indentExpr e);
        let recArg := args.get! recArgPos;
        f ← catch (toBelow below recArgInfo.indParams.size recArg) (fun _ => throwError $ "failed to eliminate recursive application" ++ indentExpr e);
        -- Recall that the fixed parameters are not in the scope of the `brecOn`. So, we skip them.
        let argsNonFixed := args.extract numFixed args.size;
        -- The function `f` does not explicitly take `recArg` and its indices as arguments. So, we skip them too.
        let fArgs := argsNonFixed.iterate #[] fun i a fArgs =>
          if recArgInfo.pos == i.val || recArgInfo.indicesPos.contains i.val then fArgs else fArgs.push a;
        pure $ mkAppN f fArgs
      else do
        f ← replaceRecApps below f;
        args ← args.mapM (replaceRecApps below);
        pure $ mkAppN f args
    };
  matcherApp? ← matchMatcherApp? e;
  match matcherApp? with
  | some matcherApp =>
    if !containsRecFn recFnName e then processApp e
    else do
      matcherApp ← mapError (matcherApp.addArg below) (fun msg => "failed to add `below` argument to 'matcher' application" ++ indentD msg);
      altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun ⟨alt, numParams⟩ =>
        lambdaTelescope alt fun xs altBody => do {
          trace! `Elab.definition.structural ("altNumParams: " ++ toString numParams ++ ", xs: " ++ xs);
          unless (xs.size >= numParams) $
            throwError $ "unexpected matcher application alternative " ++ indentExpr alt ++ Format.line ++ "at application" ++ indentExpr e;
          let belowForAlt := xs.get! (numParams - 1);
          altBodyNew ← replaceRecApps belowForAlt altBody;
          mkLambdaFVars xs altBodyNew
        };
      pure { matcherApp with alts := altsNew }.toExpr
  | none => processApp e
| _, e => ensureNoRecFn recFnName e

private def mkBRecOn (recFnName : Name) (recArgInfo : RecArgInfo) (value : Expr) : MetaM Expr := do
type ← inferType value;
let type := type.headBeta;
let major := recArgInfo.ys.get! recArgInfo.pos;
let otherArgs := recArgInfo.ys.filter fun y => y != major && !recArgInfo.indIndices.contains y;
motive ← mkForallFVars otherArgs type;
brecOnUniv ← getLevel motive;
trace! `Elab.definition.structural ("brecOn univ: " ++ brecOnUniv);
let useBInductionOn := recArgInfo.reflexive && brecOnUniv == levelZero;
brecOnUniv ← if recArgInfo.reflexive && brecOnUniv != levelZero then decLevel brecOnUniv else pure brecOnUniv;
motive ← mkLambdaFVars (recArgInfo.indIndices.push major) motive;
trace! `Elab.definition.structural ("brecOn motive: " ++ motive);
let brecOn :=
  if useBInductionOn then
    Lean.mkConst (mkBInductionOnFor recArgInfo.indName) recArgInfo.indLevels
  else
    Lean.mkConst (mkBRecOnFor recArgInfo.indName) (brecOnUniv :: recArgInfo.indLevels);
let brecOn := mkAppN brecOn recArgInfo.indParams;
let brecOn := mkApp brecOn motive;
let brecOn := mkAppN brecOn recArgInfo.indIndices;
let brecOn := mkApp brecOn major;
check brecOn;
brecOnType ← inferType brecOn;
trace! `Elab.definition.structural ("brecOn     " ++ brecOn);
trace! `Elab.definition.structural ("brecOnType " ++ brecOnType);
forallBoundedTelescope brecOnType (some 1) fun F _ => do
  let F := F.get! 0;
  FType ← inferType F;
  let numIndices := recArgInfo.indIndices.size;
  forallBoundedTelescope FType (some $ numIndices + 1 /- major -/ + 1 /- below -/ + otherArgs.size) fun Fargs _ => do
    let indicesNew   := Fargs.extract 0 numIndices;
    let majorNew     := Fargs.get! numIndices;
    let below        := Fargs.get! (numIndices+1);
    let otherArgsNew := Fargs.extract (numIndices+2) Fargs.size;
    let valueNew     := value.replaceFVars recArgInfo.indIndices indicesNew;
    let valueNew     := valueNew.replaceFVar major majorNew;
    let valueNew     := valueNew.replaceFVars otherArgs otherArgsNew;
    valueNew ← replaceRecApps recFnName recArgInfo below valueNew;
    Farg ← mkLambdaFVars Fargs valueNew;
    let brecOn := mkApp brecOn Farg;
    pure $ mkAppN brecOn otherArgs

private def elimRecursion (preDef : PreDefinition) : MetaM PreDefinition :=
withoutModifyingEnv do lambdaTelescope preDef.value fun xs value => do
  addAsAxiom preDef;
  trace! `Elab.definition.structural (preDef.declName ++ " " ++ xs ++ " :=\n" ++ value);
  let numFixed := getFixedPrefix preDef.declName xs value;
  findRecArg numFixed xs fun recArgInfo => do
    -- when (recArgInfo.indName == `Nat) throwStructuralFailed; -- HACK to skip Nat argument
    valueNew ← mkBRecOn preDef.declName recArgInfo value;
    valueNew ← mkLambdaFVars xs valueNew;
    trace! `Elab.definition.structural ("result: " ++ valueNew);
    -- Recursive applications may still occur in expressions that were not visited by replaceRecApps (e.g., in types)
    valueNew ← ensureNoRecFn preDef.declName valueNew;
    pure { preDef with value := valueNew }

def structuralRecursion (preDefs : Array PreDefinition) : TermElabM Unit :=
if preDefs.size != 1 then
  throwError "structural recursion does not handle mutually recursive functions"
else do
  preDefNonRec ← liftMetaM $ elimRecursion (preDefs.get! 0);
  addNonRec preDefNonRec;
  addAndCompileUnsafeRec preDefs

@[init] private def regTraceClasses : IO Unit := do
registerTraceClass `Elab.definition.structural;
pure ()

end Elab
end Lean
