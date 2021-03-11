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
namespace Structural
open Meta

private def getFixedPrefix (declName : Name) (xs : Array Expr) (value : Expr) : MetaM Nat := do
  let numFixedRef ← IO.mkRef xs.size
  forEachExpr' value fun e => do
    if e.isAppOf declName then
      let args := e.getAppArgs
      numFixedRef.modify fun numFixed => if args.size < numFixed then args.size else numFixed
      for arg in args, x in xs do
        /- We should not use structural equality here. For example, given the definition
           ```
           def V.map {α β} f x x_1 :=
             @V.map.match_1.{1} α (fun x x_2 => V β x) x x_1
               (fun x x_2 => @V.mk₁ β x (f Bool.true x_2))
               (fun e => @V.mk₂ β (V.map (fun b => α b) (fun b => β b) f Bool.false e))
           ```
           The first three arguments at `V.map (fun b => α b) (fun b => β b) f Bool.false e` are "fixed"
           modulo definitional equality.
        -/
        if !(← withReducible <| isDefEq arg x) then
          -- We continue searching if e's arguments are not a prefix of `xs`
          return true
      return false
    else
      return true
  numFixedRef.get

structure RecArgInfo where
  /- `fixedParams ++ ys` are the arguments of the function we are trying to justify termination using structural recursion. -/
  fixedParams : Array Expr
  ys          : Array Expr  -- recursion arguments
  pos         : Nat         -- position in `ys` of the argument we are recursing on
  indicesPos  : Array Nat   -- position in `ys` of the inductive datatype indices we are recursing on
  indName     : Name        -- inductive datatype name of the argument we are recursing on
  indLevels   : List Level  -- inductice datatype universe levels of the argument we are recursing on
  indParams   : Array Expr  -- inductive datatype parameters of the argument we are recursing on
  indIndices  : Array Expr  -- inductive datatype indices of the argument we are recursing on, it is equal to `indicesPos.map fun i => ys.get! i`
  reflexive   : Bool        -- true if we are recursing over a reflexive inductive datatype

private def getIndexMinPos (xs : Array Expr) (indices : Array Expr) : Nat := do
  let mut minPos := xs.size
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

structure State where
  /- When compiling structural recursion we use the `brecOn` recursor automatically built by
     the `inductive` command. For an inductive datatype `C`, it has the form
     `C.brecOn As motive is c F`
     where `As` are the inductive datatype parameters, `is` are the inductive datatype indices,
     `c : C As is`, and `F : (js) → (d : C As js) → C.below d → motive d`
     The `C.below d` is used to eliminate recursive applications. We refine its type when we process
     a nested dependent pattern matcher using `MatcherApp.addArg`. See `replaceRecApps` for additional details.
     We store the names of the matcher where we used `MatcherApp.addArg` at `matcherBelowDep`.
     We use this information to generate the auxiliary `_sunfold` definition needed by the smart unfolding
     technique used at WHNF. -/
  matcherBelowDep : NameSet := {}

abbrev M := StateRefT State MetaM

instance {α} : Inhabited (M α) where
  default := throwError "failed"

private def run {α} (x : M α) (s : State := {}) : MetaM (α × State) :=
  StateRefT'.run x s

private def orelse' {α} (x y : M α) : M α := do
  let saveState ← get
  orelseMergeErrors x (do set saveState; y)

private partial def findRecArg {α} (numFixed : Nat) (xs : Array Expr) (k : RecArgInfo → M α) : M α :=
  let rec loop (i : Nat) : M α := do
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
          let indParams  := indArgs.extract 0 indInfo.numParams
          let indIndices := indArgs.extract indInfo.numParams indArgs.size
          if !indIndices.all Expr.isFVar then
            orelse'
              (throwError! "argument #{i+1} was not used because its type is an inductive family and indices are not variables{indentExpr xType}")
              (loop (i+1))
          else if !indIndices.allDiff then
            orelse'
              (throwError! "argument #{i+1} was not used because its type is an inductive family and indices are not pairwise distinct{indentExpr xType}")
              (loop (i+1))
          else
            let indexMinPos := getIndexMinPos xs indIndices
            let numFixed    := if indexMinPos < numFixed then indexMinPos else numFixed
            let fixedParams := xs.extract 0 numFixed
            let ys          := xs.extract numFixed xs.size
            match ← hasBadIndexDep? ys indIndices with
            | some (index, y) =>
              orelse'
                (throwError! "argument #{i+1} was not used because its type is an inductive family{indentExpr xType}\nand index{indentExpr index}\ndepends on the non index{indentExpr y}")
                (loop (i+1))
            | none =>
              match ← hasBadParamDep? ys indParams with
              | some (indParam, y) =>
                orelse'
                  (throwError! "argument #{i+1} was not used because its type is an inductive datatype{indentExpr xType}\nand parameter{indentExpr indParam}\ndepends on{indentExpr y}")
                  (loop (i+1))
              | none =>
                let indicesPos := indIndices.map fun index => match ys.indexOf? index with | some i => i.val | none => unreachable!
                orelse'
                  (mapError
                    (k { fixedParams := fixedParams
                         ys          := ys
                         pos         := i - fixedParams.size
                         indicesPos  := indicesPos
                         indName     := indInfo.name
                         indLevels   := us
                         indParams   := indParams
                         indIndices  := indIndices
                         reflexive := indInfo.isReflexive })
                    (fun msg => m!"argument #{i+1} was not used for structural recursion{indentD msg}"))
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
    trace[Elab.definition.structural] "belowDict: {belowDict}, arg: {arg}"
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
  trace[Elab.definition.structural] "belowType: {belowType}"
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

/--
  Return true iff `e` contains an application `recFnName .. t ..` where the term `t` is
  the argument we are trying to recurse on, and it contains loose bound variables.

  We use this test to decide whether we should process a matcher-application as a regular
  applicaton or not. That is, whether we should push the `below` argument should be affected by the matcher or not.
  If `e` does not contain an application of the form `recFnName .. t ..`, then we know
  the recursion doesn't depend on any pattern variable in this matcher.
-/
private def recArgHasLooseBVarsAt (recFnName : Name) (recArgInfo : RecArgInfo) (e : Expr) : Bool :=
  let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos
  let app?   := e.find? fun e =>
     e.isAppOf recFnName && e.getAppNumArgs > recArgPos && (e.getArg! recArgPos).hasLooseBVars
  app?.isSome

private partial def replaceRecApps (recFnName : Name) (recArgInfo : RecArgInfo) (below : Expr) (e : Expr) : M Expr :=
  let rec loop : Expr → Expr → M Expr
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
      let processApp (e : Expr) : M Expr :=
        e.withApp fun f args => do
          if f.isConstOf recFnName then
            let numFixed  := recArgInfo.fixedParams.size
            let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos
            if recArgPos >= args.size then
              throwError! "insufficient number of parameters at recursive application {indentExpr e}"
            let recArg := args[recArgPos]
            -- For reflexive type, we may have nested recursive applications in recArg
            let recArg ← loop below recArg
            let f ← try toBelow below recArgInfo.indParams.size recArg catch  _ => throwError! "failed to eliminate recursive application{indentExpr e}"
            -- Recall that the fixed parameters are not in the scope of the `brecOn`. So, we skip them.
            let argsNonFixed := args.extract numFixed args.size
            -- The function `f` does not explicitly take `recArg` and its indices as arguments. So, we skip them too.
            let mut fArgs := #[]
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
        if !recArgHasLooseBVarsAt recFnName recArgInfo e then
          processApp e
        else
          /- Here is an example we currently not handle
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
          let matcherApp ← mapError (matcherApp.addArg below) (fun msg => "failed to add `below` argument to 'matcher' application" ++ indentD msg)
          modify fun s => { s with matcherBelowDep := s.matcherBelowDep.insert matcherApp.matcherName }
          let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaTelescope alt fun xs altBody => do
              trace[Elab.definition.structural] "altNumParams: {numParams}, xs: {xs}"
              unless xs.size >= numParams do
                throwError! "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let belowForAlt := xs[numParams - 1]
              mkLambdaFVars xs (← loop belowForAlt altBody)
          pure { matcherApp with alts := altsNew }.toExpr
      | none => processApp e
    | _, e => ensureNoRecFn recFnName e
  loop below e

private def mkBRecOn (recFnName : Name) (recArgInfo : RecArgInfo) (value : Expr) : M Expr := do
  let type  := (← inferType value).headBeta
  let major := recArgInfo.ys[recArgInfo.pos]
  let otherArgs := recArgInfo.ys.filter fun y => y != major && !recArgInfo.indIndices.contains y
  trace[Elab.definition.structural] "fixedParams: {recArgInfo.fixedParams}, otherArgs: {otherArgs}"
  let motive ← mkForallFVars otherArgs type
  let mut brecOnUniv ← getLevel motive
  trace[Elab.definition.structural] "brecOn univ: {brecOnUniv}"
  let useBInductionOn := recArgInfo.reflexive && brecOnUniv == levelZero
  if recArgInfo.reflexive && brecOnUniv != levelZero then
    brecOnUniv ← decLevel brecOnUniv
  let motive ← mkLambdaFVars (recArgInfo.indIndices.push major) motive
  trace[Elab.definition.structural] "brecOn motive: {motive}"
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
  trace[Elab.definition.structural] "brecOn     {brecOn}"
  trace[Elab.definition.structural] "brecOnType {brecOnType}"
  forallBoundedTelescope brecOnType (some 1) fun F _ => do
    let F := F[0]
    let FType ← inferType F
    trace[Elab.definition.structural] "FType: {FType}"
    let FType ← instantiateForall FType recArgInfo.indIndices
    let FType ← instantiateForall FType #[major]
    forallBoundedTelescope FType (some 1) fun below _ => do
      let below := below[0]
      let valueNew     ← replaceRecApps recFnName recArgInfo below value
      let Farg         ← mkLambdaFVars (recArgInfo.indIndices ++ #[major, below] ++ otherArgs) valueNew
      let brecOn       := mkApp brecOn Farg
      pure $ mkAppN brecOn otherArgs

private def elimRecursion (preDef : PreDefinition) : M PreDefinition :=
  withoutModifyingEnv do lambdaTelescope preDef.value fun xs value => do
    addAsAxiom preDef
    trace[Elab.definition.structural] "{preDef.declName} {xs} :=\n{value}"
    let numFixed ← getFixedPrefix preDef.declName xs value
    trace[Elab.definition.structural] "numFixed: {numFixed}"
    findRecArg numFixed xs fun recArgInfo => do
      -- when (recArgInfo.indName == `Nat) throwStructuralFailed -- HACK to skip Nat argument
      let valueNew ← mkBRecOn preDef.declName recArgInfo value
      let valueNew ← mkLambdaFVars xs valueNew
      trace[Elab.definition.structural] "result: {valueNew}"
      -- Recursive applications may still occur in expressions that were not visited by replaceRecApps (e.g., in types)
      let valueNew ← ensureNoRecFn preDef.declName valueNew
      pure { preDef with value := valueNew }

partial def addSmartUnfoldingDefAux (preDef : PreDefinition) (matcherBelowDep : NameSet) : MetaM PreDefinition := do
  let recFnName := preDef.declName
  let isMarkedMatcherName (n : Name) : Bool    := matcherBelowDep.contains n
  let isMarkedMatcherConst (e : Expr) : Bool   := e.isConst && isMarkedMatcherName e.constName!
  let isMarkedMatcherApp (e : Expr) : Bool     := isMarkedMatcherConst e.getAppFn
  let containsMarkedMatcher (e : Expr) : Bool := e.find? isMarkedMatcherConst |>.isSome
  let rec visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.lam ..     => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
    | Expr.forallE .. => forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
    | Expr.letE n type val body _ =>
      withLetDecl n type (← visit val) fun x => do
        mkLetFVars #[x] (← visit (body.instantiate1 x))
    | Expr.mdata d b _   => return mkMData d (← visit b)
    | Expr.proj n i s _  => return mkProj n i (← visit s)
    | Expr.app .. =>
      let processApp (e : Expr) : MetaM Expr :=
        e.withApp fun f args => do
          return mkAppN (← visit f) (← args.mapM visit)
      match isMarkedMatcherApp e, (← matchMatcherApp? e) with
      | true, some matcherApp =>
        let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
          lambdaTelescope alt fun xs altBody => do
            unless xs.size >= numParams do
              throwError! "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
            if containsMarkedMatcher altBody then
              -- continue
              mkLambdaFVars xs (← visit altBody)
            else
              -- add idRhs marker
              let altBody ← mkLambdaFVars xs[numParams:xs.size] altBody
              let altBody ← mkIdRhs altBody
              mkLambdaFVars xs[0:numParams] altBody
        pure { matcherApp with alts := altsNew }.toExpr
      | _, _ => processApp e
    | _ => pure e
  return { preDef with
    declName  := mkSmartUnfoldingNameFor preDef.declName,
    value     := (← visit preDef.value),
    modifiers := {}
  }

partial def addSmartUnfoldingDef (preDef : PreDefinition) (state : State) : TermElabM Unit := do
  if (← isProp preDef.type) then
    return ()
  else
    let preDefSUnfold ← addSmartUnfoldingDefAux preDef state.matcherBelowDep
    addNonRec preDefSUnfold

def structuralRecursion (preDefs : Array PreDefinition) : TermElabM Unit :=
  if preDefs.size != 1 then
    throwError "structural recursion does not handle mutually recursive functions"
  else do
    let (preDefNonRec, state) ← run $ elimRecursion preDefs[0]
    mapError (addNonRec preDefNonRec) (fun msg => m!"structural recursion failed, produced type incorrect term{indentD msg}")
    addAndCompilePartialRec preDefs
    addSmartUnfoldingDef preDefs[0] state

builtin_initialize
  registerTraceClass `Elab.definition.structural

end Structural

export Structural (structuralRecursion)

end Lean.Elab
