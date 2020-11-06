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
namespace Lean.Elab
open Meta

private def getFixedPrefix (declName : Name) (xs : Array Expr) (value : Expr) : Nat :=
  let visitor {ω} : StateRefT Nat (ST ω) Unit :=
    value.forEach' fun e =>
      if e.isAppOf declName then do
        let args := e.getAppArgs
        modify fun numFixed => if args.size < numFixed then args.size else numFixed
        -- we continue searching if the e's arguments are not a prefix of `xs`
        pure !args.isPrefixOf xs
      else
        pure true
  runST fun _ => do let (_, numFixed) ← visitor.run xs.size; pure numFixed

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

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := do
  let minPos := xs.size
  for index in indices do
    match xs.indexOf? index with
    | some pos => if pos.val < minPos then minPos := pos.val
    | _        => pure ()
  return minPos

-- Indices can only depend on other indices
private def hasBadIndexDep? (ys : Array Expr) (indices : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for index in indices do
    let indexType ← inferType index
    for y in ys do
      if !indices.contains y && (← dependsOn indexType y.fvarId!) then
        return some (index, y)
  return none

-- Inductive datatype parameters cannot depend on ys
private def hasBadParamDep? (ys : Array Expr) (indParams : Array Expr) : MetaM (Option (Expr × Expr)) := do
  for p in indParams do
    let pType ← inferType p
    for y in ys do
      if ← dependsOn pType y.fvarId! then
        return some (p, y)
  return none

private def throwStructuralFailed {α} : MetaM α :=
  throwError "structural recursion cannot be used"

private partial def findRecArg {α} (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → MetaM α) : MetaM α :=
  let rec loop (i : Nat) : MetaM α := do
    if h : i < xs.size then
      let x := xs.get ⟨i, h⟩
      let localDecl ← getFVarLocalDecl x
      if localDecl.isLet then
        throwStructuralFailed
      else
        let xType ← whnfD localDecl.type
        matchConstInduct xType.getAppFn (fun _ => loop (i+1)) fun indInfo us => do
        if !(← hasConst (mkBRecOnName indInfo.name)) then
          loop (i+1)
        else if indInfo.isReflexive && !(← hasConst (mkBInductionOnName indInfo.name)) then
          loop (i+1)
        else
          let indArgs    := xType.getAppArgs
          let indParams  := indArgs.extract 0 indInfo.nparams
          let indIndices := indArgs.extract indInfo.nparams indArgs.size
          if !indIndices.all Expr.isFVar then
            orelseMergeErrors
              (throwError! "argument #{i+1} was not used because its type is an inductive family and indices are not variables{indentExpr xType}")
              (loop (i+1))
          else if !indIndices.allDiff then
            orelseMergeErrors
              (throwError! "argument #{i+1} was not used because its type is an inductive family and indices are not pairwise distinct{indentExpr xType}")
              (loop (i+1))
          else
            let indexMinPos := getIndexMinPos xs indIndices
            let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
            let fixedParams := xs.extract 0 numFixed
            let ys          := xs.extract numFixed xs.size
            match ← hasBadIndexDep? ys indIndices with
            | some (index, y) =>
              orelseMergeErrors
                (throwError! "argument #{i+1} was not used because its type is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}")
                (loop (i+1))
            | none =>
              match ← hasBadParamDep? ys indParams with
              | some (indParam, y) =>
                orelseMergeErrors
                  (throwError! "argument #{i+1} was not used because its type is an inductive datatype{indentExpr xType}\nand parameter{indentExpr indParam}\ndepends on{indentExpr y}")
                  (loop (i+1))
              | none =>
                let indicesPos := indIndices.map fun index => match ys.indexOf? index with | some i => i.val | none => unreachable!
                orelseMergeErrors
                  (mapError
                    (k { fixedParams := fixedParams, ys := ys, pos := i - fixedParams.size,
                       indicesPos  := indicesPos,
                       indName     := indInfo.name,
                       indLevels   := us,
                       indParams   := indParams,
                       indIndices  := indIndices,
                       reflexive := indInfo.isReflexive })
                    (fun msg => msg!"argument #{i+1} was not used for structural recursion{indentD msg}"))
                  (loop (i+1))
    else
      throwStructuralFailed
  loop numFixed

private def containsRecFn (recFnName : Name) (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf recFnName).isSome

private def ensureNoRecFn (recFnName : Name) (e : Expr) : MetaM Expr := do
  if containsRecFn recFnName e then
    Meta.forEachExpr e fun e => do
      if e.isAppOf recFnName then
        throwError! "unexpected occurrence of recursive application{indentExpr e}"
    pure e
  else
    pure e

private def throwToBelowFailed {α} : MetaM α :=
  throwError "toBelow failed"

/- See toBelow -/
private partial def toBelowAux (C : Expr) : Expr → Expr → Expr → MetaM Expr
  | belowDict, arg, F => do
    let belowDict ← whnf belowDict
    trace[Elab.definition.structural]! "belowDict: {belowDict}, arg: {arg}"
    match belowDict with
    | Expr.app (Expr.app (Expr.const `PProd _ _) d1 _) d2 _ =>
      (do toBelowAux C d1 arg (← mkAppM `PProd.fst #[F]))
      <|>
      (do toBelowAux C d2 arg (← mkAppM `PProd.snd #[F]))
    | Expr.app (Expr.app (Expr.const `And _ _) d1 _) d2 _ =>
      (do toBelowAux C d1 arg (← mkAppM `And.left #[F]))
      <|>
      (do toBelowAux C d2 arg (← mkAppM `And.right #[F]))
    | _ => forallTelescopeReducing belowDict fun xs belowDict => do
      let argArgs := arg.getAppArgs
      unless argArgs.size >= xs.size do throwToBelowFailed
      let n := argArgs.size
      let argTailArgs := argArgs.extract (n - xs.size) n
      let belowDict := belowDict.replaceFVars xs argTailArgs
      match belowDict with
      | Expr.app belowDictFun belowDictArg _ =>
        unless belowDictFun.getAppFn == C do throwToBelowFailed
        unless ← isDefEq belowDictArg arg do throwToBelowFailed
        pure (mkAppN F argTailArgs)
      | _ => throwToBelowFailed

/- See toBelow -/
private def withBelowDict {α} (below : Expr) (numIndParams : Nat) (k : Expr → Expr → MetaM α) : MetaM α := do
  let belowType ← inferType below
  trace[Elab.definition.structural]! "belowType: {belowType}"
  belowType.withApp fun f args => do
    let motivePos := numIndParams + 1
    unless motivePos < args.size do throwError! "unexpected 'below' type{indentExpr belowType}"
    let pre := mkAppN f (args.extract 0 numIndParams)
    let preType ← inferType pre
    forallBoundedTelescope preType (some 1) fun x _ => do
      let motiveType ← inferType x[0]
      let C ← mkFreshUserName `C
      withLocalDeclD C motiveType fun C =>
        let belowDict := mkApp pre C
        let belowDict := mkAppN belowDict (args.extract (numIndParams + 1) args.size)
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

private partial def replaceRecApps (recFnName : Name) (recArgInfo : RecArgInfo) (below : Expr) (e : Expr) : MetaM Expr :=
  let rec loop : Expr → Expr → MetaM Expr
    | below, e@(Expr.lam n d b c) => do
      withLocalDecl n c.binderInfo (← loop below d) fun x => do
        mkLambdaFVars #[x] (← loop below (b.instantiate1 x))
    | below, e@(Expr.forallE n d b c) => do
      withLocalDecl n c.binderInfo (← loop below d) fun x => do
        mkForallFVars #[x] (← loop below (b.instantiate1 x))
    | below, Expr.letE n type val body _ => do
      withLetDecl n (← loop below type) (← loop below val) fun x => do
        mkLetFVars #[x] (← loop below (body.instantiate1 x))
    | below, Expr.mdata d e _   => do pure $ mkMData d (← loop below e)
    | below, Expr.proj n i e _  => do pure $ mkProj n i (← loop below e)
    | below, e@(Expr.app _ _ _) => do
      let processApp (e : Expr) : MetaM Expr :=
        e.withApp fun f args => do
          if f.isConstOf recFnName then
            let numFixed  := recArgInfo.fixedParams.size
            let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos
            if recArgPos >= args.size then
              throwError! "insufficient number of parameters at recursive application {indentExpr e}"
            let recArg := args[recArgPos]
            let f ← try toBelow below recArgInfo.indParams.size recArg catch  _ => throwError! "failed to eliminate recursive application{indentExpr e}"
            -- Recall that the fixed parameters are not in the scope of the `brecOn`. So, we skip them.
            let argsNonFixed := args.extract numFixed args.size
            -- The function `f` does not explicitly take `recArg` and its indices as arguments. So, we skip them too.
            let fArgs := #[]
            for i in [:argsNonFixed.size] do
              if recArgInfo.pos != i && !recArgInfo.indicesPos.contains i then
                let arg := argsNonFixed[i]
                let arg ← replaceRecApps recFnName recArgInfo below arg
                fArgs := fArgs.push arg
            pure $ mkAppN f fArgs
          else
            pure $ mkAppN (← loop below f) (← args.mapM (loop below))
      let matcherApp? ← matchMatcherApp? e
      match matcherApp? with
      | some matcherApp =>
        /- If none of the alternatives contain a recursive application, we process it as a regular one. -/
        if matcherApp.alts.all fun alt => !containsRecFn recFnName alt then
          processApp e
        else
          /- Here is an example we currently not handle
             ```
             def f (xs : List Nat) : Nat :=
             match xs with
             | [] => 0
             | y::ys =>
               match ys with
               | [] => 1
               | zs => f ys + 1
             ```
             We are matching on `ys`, but still using `ys` in the second alternative.
             If we push the `below` argument over the dependent match it will be able to eliminate recursive call using `zs`.
             To make it work, users have to write the second alternative as `| zs => f zs + 1`
             We considered trying `processApp e` first, and only if fails trying the code below.
             This trick is sufficient for solving the example above, but it is not sufficient for the slightly more complicated example:
             ```
             def g (xs : List Nat) : Nat :=
             match xs with
             | [] => 0
             | y::ys =>
               match ys with
               | []       => 1
               | _::_::zs => g zs + 1
               | _        => g ys + 2
             ```
             To make it work, users would have to write the last alternative as
             ```
             | zs => g zs + 2
             ```
             If this is too annoying in practice, we may replace `ys` with the matching term.
             This may generate weird error messages, when it doesn't work.
          -/
          let matcherApp ← mapError (matcherApp.addArg below) (fun msg => "failed to add `below` argument to 'matcher' application" ++ indentD msg)
          let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaTelescope alt fun xs altBody => do
              trace[Elab.definition.structural]! "altNumParams: {numParams}, xs: {xs}"
              unless xs.size >= numParams do
                throwError! "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let belowForAlt := xs[numParams - 1]
              mkLambdaFVars xs (← loop belowForAlt altBody)
          pure { matcherApp with alts := altsNew }.toExpr
      | none => processApp e
    | _, e => ensureNoRecFn recFnName e
  loop below e

private def mkBRecOn (recFnName : Name) (recArgInfo : RecArgInfo) (value : Expr) : MetaM Expr := do
  let type  := (← inferType value).headBeta
  let major := recArgInfo.ys[recArgInfo.pos]
  let otherArgs := recArgInfo.ys.filter fun y => y != major && !recArgInfo.indIndices.contains y
  let motive ← mkForallFVars otherArgs type
  let brecOnUniv ← getLevel motive
  trace[Elab.definition.structural]! "brecOn univ: {brecOnUniv}"
  let useBInductionOn := recArgInfo.reflexive && brecOnUniv == levelZero
  if recArgInfo.reflexive && brecOnUniv != levelZero then
    brecOnUniv ← decLevel brecOnUniv
  let motive ← mkLambdaFVars (recArgInfo.indIndices.push major) motive
  trace[Elab.definition.structural]! "brecOn motive: {motive}"
  let brecOn :=
    if useBInductionOn then
      Lean.mkConst (mkBInductionOnName recArgInfo.indName) recArgInfo.indLevels
    else
      Lean.mkConst (mkBRecOnName recArgInfo.indName) (brecOnUniv :: recArgInfo.indLevels)
  let brecOn := mkAppN brecOn recArgInfo.indParams
  let brecOn := mkApp brecOn motive
  let brecOn := mkAppN brecOn recArgInfo.indIndices
  let brecOn := mkApp brecOn major
  check brecOn
  let brecOnType ← inferType brecOn
  trace[Elab.definition.structural]! "brecOn     {brecOn}"
  trace[Elab.definition.structural]! "brecOnType {brecOnType}"
  forallBoundedTelescope brecOnType (some 1) fun F _ => do
    let F := F[0]
    let FType ← inferType F
    let numIndices := recArgInfo.indIndices.size
    forallBoundedTelescope FType (some $ numIndices + 1 /- major -/ + 1 /- below -/ + otherArgs.size) fun Fargs _ => do
      let indicesNew   := Fargs.extract 0 numIndices
      let majorNew     := Fargs[numIndices]
      let below        := Fargs[numIndices+1]
      let otherArgsNew := Fargs.extract (numIndices+2) Fargs.size
      let valueNew     := value.replaceFVars recArgInfo.indIndices indicesNew
      let valueNew     := valueNew.replaceFVar major majorNew
      let valueNew     := valueNew.replaceFVars otherArgs otherArgsNew
      let valueNew     ← replaceRecApps recFnName recArgInfo below valueNew
      let Farg         ← mkLambdaFVars Fargs valueNew
      let brecOn       := mkApp brecOn Farg
      pure $ mkAppN brecOn otherArgs

private def elimRecursion (preDef : PreDefinition) : MetaM PreDefinition :=
  withoutModifyingEnv do lambdaTelescope preDef.value fun xs value => do
    addAsAxiom preDef
    trace[Elab.definition.structural]! "{preDef.declName} {xs} :=\n{value}"
    let numFixed := getFixedPrefix preDef.declName xs value
    findRecArg numFixed xs fun recArgInfo => do
      -- when (recArgInfo.indName == `Nat) throwStructuralFailed -- HACK to skip Nat argument
      let valueNew ← mkBRecOn preDef.declName recArgInfo value
      let valueNew ← mkLambdaFVars xs valueNew
      trace[Elab.definition.structural]! "result: {valueNew}"
      -- Recursive applications may still occur in expressions that were not visited by replaceRecApps (e.g., in types)
      let valueNew ← ensureNoRecFn preDef.declName valueNew
      pure { preDef with value := valueNew }

def structuralRecursion (preDefs : Array PreDefinition) : TermElabM Unit :=
  if preDefs.size != 1 then
    throwError "structural recursion does not handle mutually recursive functions"
  else do
    let preDefNonRec ← elimRecursion preDefs[0]
    mapError (addNonRec preDefNonRec) (fun msg => msg!"structural recursion failed, produced type incorrect term{indentD msg}")
    addAndCompileUnsafeRec preDefs

builtin_initialize
  registerTraceClass `Elab.definition.structural

end Lean.Elab
