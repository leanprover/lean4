/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.HasConstCache
import Lean.Meta.CasesOn
import Lean.Meta.Match.Match
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

private def throwToBelowFailed : MetaM α :=
  throwError "toBelow failed"

/-- See `toBelow` -/
private partial def toBelowAux (C : Expr) (belowDict : Expr) (arg : Expr) (F : Expr) : MetaM Expr := do
  let belowDict ← whnf belowDict
  trace[Elab.definition.structural] "belowDict: {belowDict}, arg: {arg}"
  match belowDict with
  | .app (.app (.const `PProd _) d1) d2 =>
    (do toBelowAux C d1 arg (← mkAppM `PProd.fst #[F]))
    <|>
    (do toBelowAux C d2 arg (← mkAppM `PProd.snd #[F]))
  | .app (.app (.const `And _) d1) d2 =>
    (do toBelowAux C d1 arg (← mkAppM `And.left #[F]))
    <|>
    (do toBelowAux C d2 arg (← mkAppM `And.right #[F]))
  | _ => forallTelescopeReducing belowDict fun xs belowDict => do
    let arg ← zetaReduce arg
    let argArgs := arg.getAppArgs
    unless argArgs.size >= xs.size do throwToBelowFailed
    let n := argArgs.size
    let argTailArgs := argArgs.extract (n - xs.size) n
    let belowDict := belowDict.replaceFVars xs argTailArgs
    match belowDict with
    | .app belowDictFun belowDictArg =>
      unless belowDictFun.getAppFn == C do throwToBelowFailed
      unless ← isDefEq belowDictArg arg do throwToBelowFailed
      pure (mkAppN F argTailArgs)
    | _ => throwToBelowFailed

/-- See `toBelow` -/
private def withBelowDict (below : Expr) (numIndParams : Nat) (k : Expr → Expr → MetaM α) : MetaM α := do
  let belowType ← inferType below
  trace[Elab.definition.structural] "belowType: {belowType}"
  belowType.withApp fun f args => do
    let motivePos := numIndParams + 1
    unless motivePos < args.size do throwError "unexpected 'below' type{indentExpr belowType}"
    let pre := mkAppN f (args.extract 0 numIndParams)
    let preType ← inferType pre
    forallBoundedTelescope preType (some 1) fun x _ => do
      let motiveType ← inferType x[0]!
      withLocalDeclD (← mkFreshUserName `C) motiveType fun C =>
        let belowDict := mkApp pre C
        let belowDict := mkAppN belowDict (args.extract (numIndParams + 1) args.size)
        k C belowDict

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
private partial def toBelow (below : Expr) (numIndParams : Nat) (recArg : Expr) : MetaM Expr := do
  withBelowDict below numIndParams fun C belowDict =>
    toBelowAux C belowDict recArg below

/--
  This method is used after `matcherApp.addArg arg` to check whether the new type of `arg` has been "refined/modified"
  in at least one alternative.
-/
def refinedArgType (matcherApp : MatcherApp) (arg : Expr) : MetaM Bool := do
  let argType ← inferType arg
  (Array.zip matcherApp.alts matcherApp.altNumParams).anyM fun (alt, numParams) =>
    lambdaTelescope alt fun xs _ => do
      if xs.size >= numParams then
        let refinedArg := xs[numParams - 1]!
        return !(← isDefEq (← inferType refinedArg) argType)
      else
        return false

private partial def replaceRecApps (recFnName : Name) (recArgInfo : RecArgInfo) (below : Expr) (e : Expr) : M Expr :=
  let containsRecFn (e : Expr) : StateRefT (HasConstCache recFnName) M Bool :=
    modifyGet (·.contains e)
  let rec loop (below : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) M Expr := do
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
      let processApp (e : Expr) : StateRefT (HasConstCache recFnName) M Expr :=
        e.withApp fun f args => do
          if f.isConstOf recFnName then
            let numFixed  := recArgInfo.fixedParams.size
            let recArgPos := recArgInfo.fixedParams.size + recArgInfo.pos
            if recArgPos >= args.size then
              throwError "insufficient number of parameters at recursive application {indentExpr e}"
            let recArg := args[recArgPos]!
            -- For reflexive type, we may have nested recursive applications in recArg
            let recArg ← loop below recArg
            let f ← try toBelow below recArgInfo.indParams.size recArg catch  _ => throwError "failed to eliminate recursive application{indentExpr e}"
            -- Recall that the fixed parameters are not in the scope of the `brecOn`. So, we skip them.
            let argsNonFixed := args.extract numFixed args.size
            -- The function `f` does not explicitly take `recArg` and its indices as arguments. So, we skip them too.
            let mut fArgs := #[]
            for i in [:argsNonFixed.size] do
              if recArgInfo.pos != i && !recArgInfo.indicesPos.contains i then
                let arg := argsNonFixed[i]!
                let arg ← replaceRecApps recFnName recArgInfo below arg
                fArgs := fArgs.push arg
            return mkAppN f fArgs
          else
            return mkAppN (← loop below f) (← args.mapM (loop below))
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !recArgHasLooseBVarsAt recFnName recArgInfo.recArgPos e then
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
          let matcherApp ← mapError (matcherApp.addArg below) (fun msg => "failed to add `below` argument to 'matcher' application" ++ indentD msg)
          if !(← refinedArgType matcherApp below) then
            processApp e
          else
            let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
              lambdaTelescope alt fun xs altBody => do
                trace[Elab.definition.structural] "altNumParams: {numParams}, xs: {xs}"
                unless xs.size >= numParams do
                  throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
                let belowForAlt := xs[numParams - 1]!
                mkLambdaFVars xs (← loop belowForAlt altBody)
            pure { matcherApp with alts := altsNew }.toExpr
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !recArgHasLooseBVarsAt recFnName recArgInfo.recArgPos e then
          processApp e
        else if let some casesOnApp ← casesOnApp.addArg? below (checkIfRefined := true) then
          let altsNew ← (Array.zip casesOnApp.alts casesOnApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaTelescope alt fun xs altBody => do
              unless xs.size >= numParams do
                throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
              let belowForAlt := xs[numParams]!
              mkLambdaFVars xs (← loop belowForAlt altBody)
          return { casesOnApp with alts := altsNew }.toExpr
        else
          processApp e
      | none => processApp e
    | e => ensureNoRecFn recFnName e
  loop below e |>.run' {}

def mkBRecOn (recFnName : Name) (recArgInfo : RecArgInfo) (value : Expr) : M Expr := do
  trace[Elab.definition.structural] "mkBRecOn: {value}"
  let type  := (← inferType value).headBeta
  let major := recArgInfo.ys[recArgInfo.pos]!
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
    let F := F[0]!
    let FType ← inferType F
    trace[Elab.definition.structural] "FType: {FType}"
    let FType ← instantiateForall FType recArgInfo.indIndices
    let FType ← instantiateForall FType #[major]
    forallBoundedTelescope FType (some 1) fun below _ => do
      -- TODO: `below` user name is `f`, and it will make a global `f` to be pretty printed as `_root_.f` in error messages.
      -- We should add an option to `forallBoundedTelescope` to ensure fresh names are used.
      let below := below[0]!
      let valueNew     ← replaceRecApps recFnName recArgInfo below value
      let Farg         ← mkLambdaFVars (recArgInfo.indIndices ++ #[major, below] ++ otherArgs) valueNew
      let brecOn       := mkApp brecOn Farg
      return mkAppN brecOn otherArgs

end Lean.Elab.Structural
