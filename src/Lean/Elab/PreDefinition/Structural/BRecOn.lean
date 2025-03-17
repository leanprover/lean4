/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Joachim Breitner
-/
prelude
import Lean.Util.HasConstCache
import Lean.Meta.PProdN
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.Structural.RecArgInfo

namespace Lean.Elab.Structural
open Meta

private def throwToBelowFailed : MetaM α :=
  throwError "toBelow failed"

partial def searchPProd (e : Expr) (F : Expr) (k : Expr → Expr → MetaM α) : MetaM α := do
  match (← whnf e) with
  | .app (.app (.const `PProd _) d1) d2 =>
        (do searchPProd d1 (.proj ``PProd 0 F) k)
    <|> (do searchPProd d2 (.proj ``PProd 1 F) k)
  | .app (.app (.const `And _) d1) d2 =>
        (do searchPProd d1 (.proj `And 0 F) k)
    <|> (do searchPProd d2 (.proj `And 1 F) k)
  | .const `PUnit _
  | .const `True _ => throwToBelowFailed
  | _ => k e F

/-- See `toBelow` -/
private partial def toBelowAux (C : Expr) (belowDict : Expr) (arg : Expr) (F : Expr) : MetaM Expr := do
  trace[Elab.definition.structural] "belowDict start:{indentExpr belowDict}\narg:{indentExpr arg}"
  -- First search through the PProd packing of the different `brecOn` motives
  searchPProd belowDict F fun belowDict F => do
    trace[Elab.definition.structural] "belowDict step 1:{indentExpr belowDict}"
    -- Then instantiate parameters of a reflexive type, if needed
    forallTelescopeReducing belowDict fun xs belowDict => do
      let arg ← zetaReduce arg
      let argArgs := arg.getAppArgs
      unless argArgs.size >= xs.size do throwToBelowFailed
      let n := argArgs.size
      let argTailArgs := argArgs.extract (n - xs.size) n
      let belowDict := belowDict.replaceFVars xs argTailArgs
      -- And again search through the PProd packing due to multiple functions recursing on the
      -- same inductive data type
      -- (We could use the funIdx and the `positions` array to replace this search with more
      -- targeted indexing.)
      searchPProd belowDict (mkAppN F argTailArgs) fun belowDict F => do
        trace[Elab.definition.structural] "belowDict step 2:{indentExpr belowDict}"
        match belowDict with
        | .app belowDictFun belowDictArg =>
          unless belowDictFun.getAppFn == C do throwToBelowFailed
          unless ← isDefEq belowDictArg arg do throwToBelowFailed
          pure F
        | _ =>
          trace[Elab.definition.structural] "belowDict not an app:{indentExpr belowDict}"
          throwToBelowFailed

/-- See `toBelow` -/
private def withBelowDict [Inhabited α] (below : Expr) (numIndParams : Nat)
    (positions : Positions) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let numTypeFormers := positions.size
  let belowType ← inferType below
  trace[Elab.definition.structural] "belowType: {belowType}"
  unless (← isTypeCorrect below) do
    trace[Elab.definition.structural] "not type correct!"
  belowType.withApp fun f args => do
    unless numIndParams + numTypeFormers < args.size do
      trace[Elab.definition.structural] "unexpected 'below' type{indentExpr belowType}"
      throwToBelowFailed
    let params := args[:numIndParams]
    let finalArgs := args[numIndParams+numTypeFormers:]
    let pre := mkAppN f params
    let motiveTypes ← inferArgumentTypesN numTypeFormers pre
    let numMotives : Nat := positions.numIndices
    trace[Elab.definition.structural] "numMotives: {numMotives}"
    let mut CTypes := Array.mkArray numMotives (.sort 37) -- dummy value
    for poss in positions, motiveType in motiveTypes do
      for pos in poss do
        CTypes := CTypes.set! pos motiveType
    let CDecls : Array (Name × (Array Expr → MetaM Expr)) ← CTypes.mapM fun t => do
        return ((← mkFreshUserName `C), fun _ => pure t)
    withLocalDeclsD CDecls fun Cs => do
      -- We have to pack these canary motives like we packed the real motives
      let packedCs ← positions.mapMwith PProdN.packLambdas motiveTypes Cs
      let belowDict := mkAppN pre packedCs
      let belowDict := mkAppN belowDict finalArgs
      trace[Elab.definition.structural] "initial belowDict for {Cs}:{indentExpr belowDict}"
      unless (← isTypeCorrect belowDict) do
        trace[Elab.definition.structural] "not type correct!"
      k Cs belowDict

/--
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
private partial def toBelow (below : Expr) (numIndParams : Nat) (positions : Positions) (fnIndex : Nat) (recArg : Expr) : MetaM Expr := do
  withTraceNode `Elab.definition.structural (return m!"{exceptEmoji ·} searching IH for {recArg} in {←inferType below}") do
    withBelowDict below numIndParams positions fun Cs belowDict =>
      toBelowAux Cs[fnIndex]! belowDict recArg below

private partial def replaceRecApps (recArgInfos : Array RecArgInfo) (positions : Positions)
    (below : Expr) (e : Expr) : M Expr :=
  let recFnNames := recArgInfos.map (·.fnName)
  let containsRecFn (e : Expr) : StateRefT (HasConstCache recFnNames) M Bool :=
    modifyGet (·.contains e)
  let rec loop (below : Expr) (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr := do
    if !(← containsRecFn e) then
      return e
    match e with
    | Expr.lam n d b c =>
      withLocalDecl n c (← loop below d) fun x => do
        mkLambdaFVars #[x] (← loop below (b.instantiate1 x))
    | Expr.forallE n d b c =>
      withLocalDecl n c (← loop below d) fun x => do
        mkForallFVars #[x] (← loop below (b.instantiate1 x))
    | Expr.letE n type val body _ =>
      withLetDecl n (← loop below type) (← loop below val) fun x => do
        mkLetFVars #[x] (← loop below (body.instantiate1 x)) (usedLetOnly := false)
    | Expr.mdata d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop below b
      else
        return mkMData d (← loop below b)
    | Expr.proj n i e => return mkProj n i (← loop below e)
    | Expr.app _ _ =>
      let processApp (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr :=
        e.withApp fun f args => do
          if let .some fnIdx := recArgInfos.findFinIdx? (f.isConstOf ·.fnName) then
            let recArgInfo := recArgInfos[fnIdx]
            let some recArg := args[recArgInfo.recArgPos]?
              | throwError "insufficient number of parameters at recursive application {indentExpr e}"
            -- For reflexive type, we may have nested recursive applications in recArg
            let recArg ← loop below recArg
            let f ←
              try toBelow below recArgInfo.indGroupInst.params.size positions fnIdx recArg
              catch _ => throwError "failed to eliminate recursive application{indentExpr e}"
            -- We don't pass the fixed parameters, the indices and the major arg to `f`, only the rest
            let ys := recArgInfo.fixedParamPerm.pickVarying args
            let (_, fArgs) := recArgInfo.pickIndicesMajor ys
            let fArgs ← fArgs.mapM (replaceRecApps recArgInfos positions below ·)
            return mkAppN f fArgs
          else
            return mkAppN (← loop below f) (← args.mapM (loop below))
      match (← matchMatcherApp? (alsoCasesOn := true) e) with
      | some matcherApp =>
        if recArgInfos.all (fun recArgInfo => !recArgHasLooseBVarsAt recArgInfo.fnName recArgInfo.recArgPos e) then
          processApp e
        else
          /- Here is an example we currently do not handle
             ```
             def g (xs : List Nat) : Nat :=
             match xs with
             | [] => 0
             | y::ys =>
               match ys with
               | []       => 1
               | _::_::zs => g zs + 1
               | zs       => g ys + 2
             ```
             We are matching on `ys`, but still using `ys` in the third alternative.
             If we push the `below` argument over the dependent match it will be able to eliminate recursive call using `zs`.
             To make it work, users have to write the third alternative as `| zs => g zs + 2`
             If this is too annoying in practice, we may replace `ys` with the matching term, but
             this may generate weird error messages, when it doesn't work. -/
          trace[Elab.definition.structural] "below before matcherApp.addArg: {below} : {← inferType below}"
          if let some matcherApp ← matcherApp.addArg? below then
            let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
              lambdaBoundedTelescope alt numParams fun xs altBody => do
                trace[Elab.definition.structural] "altNumParams: {numParams}, xs: {xs}"
                unless xs.size = numParams do
                  throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
                let belowForAlt := xs[numParams - 1]!
                mkLambdaFVars xs (← loop belowForAlt altBody)
            pure { matcherApp with alts := altsNew }.toExpr
          else
            processApp e
      | none => processApp e
    | e =>
      ensureNoRecFn recFnNames e
      pure e
  loop below e |>.run' {}

/--
Calculates the `.brecOn` motive corresponding to one structural recursive function.
The `value` is the function with (only) the fixed parameters moved into the context.
-/
def mkBRecOnMotive (recArgInfo : RecArgInfo) (value : Expr) : M Expr := do
  lambdaTelescope value fun xs value => do
    let type  := (← inferType value).headBeta
    let (indexMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor xs
    let motive ← mkForallFVars otherArgs type
    mkLambdaFVars indexMajorArgs motive

/--
Calculates the `.brecOn` functional argument corresponding to one structural recursive function.
The `value` is the function with (only) the fixed parameters moved into the context,
The `FType` is the expected type of the argument.
The `recArgInfos` is used to transform the body of the function to replace recursive calls with
uses of the `below` induction hypothesis.
-/
def mkBRecOnF (recArgInfos : Array RecArgInfo) (positions : Positions)
    (recArgInfo : RecArgInfo) (value : Expr) (FType : Expr) : M Expr := do
  lambdaTelescope value fun xs value => do
    let (indicesMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor xs
    let FType ← instantiateForall FType indicesMajorArgs
    forallBoundedTelescope FType (some 1) fun below _ => do
      -- TODO: `below` user name is `f`, and it will make a global `f` to be pretty printed as `_root_.f` in error messages.
      -- We should add an option to `forallBoundedTelescope` to ensure fresh names are used.
      let below := below[0]!
      let valueNew ← replaceRecApps recArgInfos positions below value
      mkLambdaFVars (indicesMajorArgs ++ #[below] ++ otherArgs) valueNew

/--
Given the `motives`, figures out whether to use `.brecOn` or `.binductionOn`, pass
the right universe levels, the parameters, and the motives.
It was already checked earlier in `checkCodomainsLevel` that the functions live in the same universe.
-/
def mkBRecOnConst (recArgInfos : Array RecArgInfo) (positions : Positions)
   (motives : Array Expr) : MetaM (Nat → Expr) := do
  let indGroup := recArgInfos[0]!.indGroupInst
  let motive := motives[0]!
  let brecOnUniv ← lambdaTelescope motive fun _ type => getLevel type
  let indInfo ← getConstInfoInduct indGroup.all[0]!
  let useBInductionOn := indInfo.isReflexive && brecOnUniv == levelZero
  let brecOnUniv ←
    if indInfo.isReflexive && brecOnUniv != levelZero then
      decLevel brecOnUniv
    else
      pure brecOnUniv
  let brecOnCons := fun idx => indGroup.brecOn useBInductionOn brecOnUniv idx
  -- Pick one as a prototype
  let brecOnAux := brecOnCons 0
  -- Infer the type of the packed motive arguments
  let packedMotiveTypes ← inferArgumentTypesN indGroup.numMotives brecOnAux
  let packedMotives ← positions.mapMwith PProdN.packLambdas packedMotiveTypes motives

  return fun n => mkAppN (brecOnCons n) packedMotives

/--
Given the `recArgInfos` and the `motives`, infer the types of the `F` arguments to the `.brecOn`
combinators. This assumes that all `.brecOn` functions of a mutual inductive have the same structure.

It also undoes the permutation and packing done by `packMotives`
-/
def inferBRecOnFTypes (recArgInfos : Array RecArgInfo) (positions : Positions)
    (brecOnConst : Nat → Expr) : MetaM (Array Expr) := do
  let numTypeFormers := positions.size
  let recArgInfo := recArgInfos[0]! -- pick an arbitrary one
  let brecOn := brecOnConst recArgInfo.indIdx
  check brecOn
  let brecOnType ← inferType brecOn
  -- Skip the indices and major argument
  let packedFTypes ← forallBoundedTelescope brecOnType (some (recArgInfo.indicesPos.size + 1)) fun _ brecOnType =>
    -- And return the types of the next arguments
    arrowDomainsN numTypeFormers brecOnType

  let mut FTypes := Array.mkArray positions.numIndices (Expr.sort 0)
  for packedFType in packedFTypes, poss in positions do
    for pos in poss do
      FTypes := FTypes.set! pos packedFType
  return FTypes

/--
Completes the `.brecOn` for the given function.
The `value` is the function with (only) the fixed parameters moved into the context.
-/
def mkBrecOnApp (positions : Positions) (fnIdx : Nat) (brecOnConst : Nat → Expr)
    (FArgs : Array Expr) (recArgInfo : RecArgInfo) (value : Expr) : MetaM Expr := do
  lambdaTelescope value fun ys _value => do
    let (indexMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor ys
    let brecOn := brecOnConst recArgInfo.indIdx
    let brecOn := mkAppN brecOn indexMajorArgs
    let packedFTypes ← inferArgumentTypesN positions.size brecOn
    let packedFArgs ← positions.mapMwith PProdN.mkLambdas packedFTypes FArgs
    let brecOn := mkAppN brecOn packedFArgs
    let some (size, idx) := positions.findSome? fun pos => (pos.size, ·) <$> pos.finIdxOf? fnIdx
      | throwError "mkBrecOnApp: Could not find {fnIdx} in {positions}"
    let brecOn ← PProdN.projM size idx brecOn
    mkLambdaFVars ys (mkAppN brecOn otherArgs)

end Lean.Elab.Structural
