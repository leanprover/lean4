/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude

public import Lean.Elab.Term
public import Lean.Elab.PreDefinition.PartialFixpoint
public section
namespace Lean.Elab.Command
open Lean Meta Elab

structure CoinductiveElabData where
  declName : Name
  ref : Syntax
  modifiers : Modifiers
  ctorSyntax : Array Syntax
  isGreatest : Bool
  deriving Inhabited

public def addFunctorPostfix : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s => Name.str p (s ++ "_functor")
  | Name.num p n => Name.num (addFunctorPostfix p) n

public def removeFunctorPostfix : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s => Name.str p (s.stripSuffix "_functor")
  | Name.num p n => Name.num (removeFunctorPostfix p) n

public def removeFunctorPostfixInCtor : Name → Name
  | Name.anonymous => Name.anonymous
  | Name.str p s => Name.str (removeFunctorPostfix p) s
  | Name.num p n => Name.num (removeFunctorPostfixInCtor p) n

private def generateCoinductiveConstructor (infos : Array InductiveVal) (ctorSyntax : Syntax)
    (numParams : Nat) (name : Name) (ctor : ConstructorVal) : TermElabM Unit := do
  trace[Elab.coinductive] "Generating constructor: {removeFunctorPostfixInCtor ctor.name}"
  let numPreds := infos.size
  let predNames := infos.map fun val => removeFunctorPostfix val.name
  let levelParams := infos[0]!.levelParams.map mkLevelParam
  /-
    We start by looking at the type of the constructor and introducing
    all its parameters to the scope
  -/
  forallBoundedTelescope ctor.type (numParams + numPreds) fun args body => do
    /-
      The first `numParams` many items of `args` are parameters from the original definition,
      while the remaining ones are free variables that correspond to recursive calls
    -/
    let params := args.take numParams
    let predFVars := args.extract numParams
    /-
      We will fill recursive calls in the body with the just defined (co)inductive predicates.
    -/
    let mut predicates : Array Expr := predNames.map (mkConst · levelParams)
    predicates := predicates.map (mkAppN · params)
    let body := body.replaceFVars predFVars predicates
    /-
      Now, we look at the rest of the constructor.
      We start by collecting its non-parameter premises, as well as inspecting its conclusion.
    -/
    let res ← forallTelescope body fun bodyArgs bodyExpr => do
      /-
        First, we look at conclusion and pick out all arguments that are non-parameters.
      -/
      let bodyAppArgs := bodyExpr.getAppArgs.extract (numParams + infos.size)
      /-
        The goal (i.e. right hands side of a constructor) that we are trying to make is just
        the coinductive predicate with parameters and non-parameter arguments applied.
      -/
      let goalType := mkConst (removeFunctorPostfix name) levelParams
      let mut goalType := mkAppN goalType params
      goalType := mkAppN goalType bodyAppArgs
      trace[Elab.coinductive] "The conclusion of the constructor {ctor.name} is {goalType}"

      -- We start by making the metavariable for it, that we will fill
      let goal ← mkFreshExprMVar <| .some goalType
      let hole := Expr.mvarId! goal

      /-
        First, we will reply on the unrolling rule that is registered by `PartialFixpoint` machinery
      -/
      let some fixEq
        ← PartialFixpoint.getUnfoldFor? (removeFunctorPostfix name) | throwError "No unfold lemma"
      let mut fixEq := mkConst fixEq levelParams
      fixEq := mkAppN fixEq params
      /-
        The right hands side of the unrolling rule is existential form of the functor defining
        the predicate with all its arguments applied
      -/
      let mut unfolded := mkConst (name ++ `existential) levelParams
      unfolded ← unfoldDefinition unfolded
      unfolded := mkAppN unfolded bodyExpr.getAppArgs
      unfolded ← whnf unfolded
      /-
        Before we apply the unrolling lemma, we need to bring it to the appropriate form,
        in which all arguments are applied
      -/
      for arg in bodyAppArgs do
        fixEq ← mkAppM ``congrFun #[fixEq, arg]
      /-
        We rewrite by the unrolling rule, the goal is now in the existential form
      -/
      let hole ← Lean.MVarId.replaceTargetEq hole unfolded fixEq
      /-
        To bring it to the inductive type form (of the original functor), we need to apply
        the lemma that connects both. We instantiate it, and get an appropriate implication.
      -/
      let equivLemmaName := name ++ `sop
      let mut equivLemma := mkConst equivLemmaName levelParams
      equivLemma := mkAppN equivLemma bodyExpr.getAppArgs
      equivLemma ← mkAppM ``Iff.mp #[equivLemma]
      let [hole] ← hole.apply equivLemma | throwError "Could not apply {equivLemmaName}"
      /-
        Now, all it suffices is to call an approprate constructor of the functor
        in the inductive type form.
      -/
      let constructor := mkConst ctor.name levelParams
      let constructor := mkAppN constructor params
      let constructor := mkAppN constructor predicates
      let constructor := mkAppN constructor bodyArgs
      hole.assign constructor
      let conclusion ← instantiateMVars goal
      let conclusion ← mkLambdaFVars bodyArgs conclusion
      mkLambdaFVars params conclusion
    let type ← inferType res
    trace[Elab.coinductive] "The elaborated constructor is of the type: {type}"
    /-
      We finish by registering the appropriate declaration
    -/
    addDecl <| .defnDecl {
      name := removeFunctorPostfixInCtor ctor.name
      levelParams := ctor.levelParams
      type := type
      value := res
      hints := .opaque
      safety := .safe
    }

    Term.addTermInfo' ctorSyntax res (isBinder := true)

private def generateCoinductiveConstructors (numParams : Nat) (infos : Array InductiveVal)
    (coinductiveElabData : Array CoinductiveElabData) : TermElabM Unit := do
  for indType in infos, e in coinductiveElabData do
    for ctor in indType.ctors, ctorSyntax in e.ctorSyntax do
      generateCoinductiveConstructor infos ctorSyntax numParams indType.name
        <| ←getConstInfoCtor ctor

def elabCoinductive (coinductiveElabData : Array CoinductiveElabData) : TermElabM Unit := do
  trace[Elab.coinductive] "Elaborating: {coinductiveElabData.map (·.declName)}"
  let infos ← coinductiveElabData.mapM (getConstInfoInduct ·.declName)
  let levelParams := infos[0]!.levelParams.map mkLevelParam
  /-
    We infer original names and types of the predicates.
    To get such names, we need to remove `_functor` postfix. At the same time,
    we need to forget about the parameters for recursive calls, to get the original types.
  -/
  let originalNumParams := infos[0]!.numParams - infos.size
  let namesAndTypes : Array (Name × Expr) ← infos.mapM fun info => do
    let type ← forallTelescope info.type fun args body => do
      mkForallFVars (args.take originalNumParams ++ args.extract info.numParams) body
    return (removeFunctorPostfix (info.name), type)
  /-
    We make dummy constants that are used in populating PreDefinitions
  -/
  let consts := namesAndTypes.map fun (name, _) => (mkConst name levelParams)
  for const in consts, e in coinductiveElabData do
    Term.addTermInfo' e.ref const (isBinder := true)
  /-
    We create values of each of PreDefinitions, by taking existential (see `Meta.SumOfProducts`)
    form of the associated functors and applying paramaters, as well as recursive calls
    (with their parameters passed).
  -/
  let preDefVals ← forallBoundedTelescope infos[0]!.type originalNumParams fun params _ => do
    infos.mapM fun info => do
      let mut functor := mkConst (info.name ++ `existential) levelParams
      functor ← unfoldDefinition functor
      functor := mkAppN functor <| params ++ consts.map (mkAppN · <| params)
      mkLambdaFVars params functor
  /-
    Finally, we populate the PreDefinitions
  -/
  let preDefs : Array PreDefinition := preDefVals.mapIdx fun idx defn =>
    { ref := coinductiveElabData[idx]!.ref
      kind := .def
      levelParams := infos[0]!.levelParams
      modifiers := coinductiveElabData[idx]!.modifiers
      declName := namesAndTypes[idx]!.1
      type := namesAndTypes[idx]!.2
      value := defn
      termination := {
        ref := coinductiveElabData[idx]!.ref
        terminationBy?? := .none
        terminationBy? := .none
        partialFixpoint? := .some {
            ref := coinductiveElabData[idx]!.ref
            term? := .none
            fixpointType := if coinductiveElabData[idx]!.isGreatest then
                              .coinductiveFixpoint else .inductiveFixpoint
        }
        decreasingBy? := .none
        extraParams := 0
      }
    }
  partialFixpoint preDefs
  generateCoinductiveConstructors originalNumParams infos coinductiveElabData

end Lean.Elab.Command
