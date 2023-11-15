/-
Copyright (c) 2023 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/

import Lean.Util.HasConstCache
import Lean.Meta.CasesOn
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Refl
import Lean.Elab.Quotation
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.WF.TerminationHint


/-!
This module finds lexicographic termination arguments for well-founded recursion.

Starting with basic measures (`sizeOf xᵢ` for all parameters `xᵢ`), it tries all combinations
until it finds one where all proof obligations go through with the given tactic (`decerasing_by`),
if given, or the default `decreasing_tactic`.

For mutual recursion, a single measure is not just one parameter, but one from each recursive
function. Enumerating these can lead to a combinatoric explosion, so we bound
the nubmer of measures tried.

In addition to measures derived from `sizeOf xᵢ`, it also considers measures
that assign an order to the functions themselves. This way we can support mutual
function definitions where no arguments decrease from one function to another.


The result of this module is a `TerminationWF`, which is then passed on to `wfRecursion`; this
design is crucial so that whatever we infer in this module could also be written manually by the
user. It would be bad if there are function definitions that can only be processed with the
guessed lexicographic order.

The following optimizations are applied to make this feasible:

1. The crucial optimiziation is to look at each argument of each recursive call
   _once_, try to prove `<` and (if that fails `≤`), and then look at that table to
   pick a suitable measure.

2. The next-crucial optimization is to fill that table lazily.  This way, we run the (likely
   expensive) tactics as few times as possible, while still being able to consider a possibly
   large number of combinations.

3. Before we even try to prove `<`, we check if the arguments are equal (`=`). No well-founded
   measure will relate equal terms, likely this check is faster than firing up the tactic engine,
   and it adds more signal to the output.

4. Instead of traversing the whole function body over and over, we traverse it once and store
   the arguments (in unpacked form) and the local `MetaM` state at each recursive call
   (see `collectRecCalls`), which we then re-use for the possibly many proof attempts.

The logic here is based on “Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL”
by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow, 10.1007/978-3-540-74591-4_5
<https://www21.in.tum.de/~nipkow/pubs/tphols07.pdf>.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Lean.Elab.WF.GuessLex

/--
Given a predefinition, find good variable names for its parameters.
Use user-given parameter names if present; use x1...xn otherwise.
The length of the returned array is also used to determine the arity
of the function, so it should match what `packDomain` does.
-/
-- TODO: Maybe the eta-expansion handling `fun foo : … | n -> ` should try to use
-- a nicer name than simply `x`?
def naryVarNames (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Name):= do
  lambdaTelescope preDef.value fun xs _ => do
    let xs := xs.extract fixedPrefixSize xs.size
    let mut ns := #[]
    for i in List.range xs.size do
      let n ← xs[i]!.fvarId!.getUserName
      if n.hasMacroScopes then
      -- TODO: Prettier code to generate x1...xn
        ns := ns.push (← mkFreshUserName (.mkSimple ("x" ++ (repr (i+1)).pretty)))
      else
        ns := ns.push n
    return ns


/-- Given
  - matcherApp `match_i As (fun xs => motive[xs]) discrs (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining`, and
  - expression `e : B[discrs]`,
  returns the expressions `B[C_1[ys_1]])  ... B[C_n[ys_n]]`,
  with `ys_i` as loose bound variables, ready to be `.instantiateRev`d; arity according to `matcherApp.altNumParams`.
  Cf. `MatcherApp.addArg`.
-/
-- PR'ed at https://github.com/leanprover/lean4/pull/2882
def _root_.Lean.Meta.MatcherApp.transform (matcherApp : MatcherApp) (e : Expr) :
    MetaM (Array Expr) :=
  lambdaTelescope matcherApp.motive fun motiveArgs _motiveBody => do
    trace[Elab.definition.wf] "MatcherApp.transform {indentExpr e}"
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "failed to transfer argument through matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"

    let eAbst ← matcherApp.discrs.size.foldRevM (init := e) fun i eAbst => do
      let motiveArg := motiveArgs[i]!
      let discr     := matcherApp.discrs[i]!
      let eTypeAbst ← kabstract eAbst discr
      return eTypeAbst.instantiate1 motiveArg
    let eEq ← mkEq eAbst eAbst

    let matcherLevels ← match matcherApp.uElimPos? with
      | none     => pure matcherApp.matcherLevels
      | some pos =>
        pure <| matcherApp.matcherLevels.set! pos levelZero
    let motive ← mkLambdaFVars motiveArgs eEq
    let aux := mkAppN (mkConst matcherApp.matcherName matcherLevels.toList) matcherApp.params
    let aux := mkApp aux motive
    let aux := mkAppN aux matcherApp.discrs
    unless (← isTypeCorrect aux) do
      throwError "failed to transfer argument through matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altAuxs, _, _) ← Lean.Meta.forallMetaTelescope auxType
    let altAuxTys ← altAuxs.mapM (inferType ·)
    (Array.zip matcherApp.altNumParams altAuxTys).mapM fun (altNumParams, altAuxTy) => do
      let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAuxTy
      unless fvs.size = altNumParams do
        throwError "failed to transfer argument through matcher application, alt type must be telescope with #{altNumParams} arguments"
      -- extract type from our synthetic equality
      let body := body.getArg! 2
      -- and abstract over the parameters of the alternatives, so that we can safely pass the Expr out
      Expr.abstractM body fvs

/-- A non-failing version of `transform` -/
-- PR'ed at https://github.com/leanprover/lean4/pull/2882
def _root_.Lean.Meta.MatcherApp.transform? (matcherApp : MatcherApp) (e : Expr) :
    MetaM (Option (Array Expr)) :=
  try
    return some (← matcherApp.transform e)
  catch _ =>
    return none


/--
  Given a `casesOn` application `c` of the form
  ```
  casesOn As (fun is x => motive[i, xs]) is major  (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining
  ```
  and a type `e : B[is, major]`, for every alternative `i`, construct the type
  ```
  B[C_i[ys_i]]
  ```
  with `ys_i` as loose bound variables, ready to be `.instantiateRev`d; arity according to `CasesOnApp.altNumParams`.
-/
-- PR'ed at https://github.com/leanprover/lean4/pull/2882
def _root_.Lean.Meta.CasesOnApp.transform (c : CasesOnApp) (e : Expr) :
    MetaM (Array Expr) :=
  lambdaTelescope c.motive fun motiveArgs _motiveBody => do
    trace[Elab.definition.wf] "CasesOnApp.transform: {indentExpr e}"
    unless motiveArgs.size == c.indices.size + 1 do
      throwError "failed to transfer argument through `casesOn` application, motive must be lambda expression with #{c.indices.size + 1} binders"
    let discrs := c.indices ++ #[c.major]
    let mut eAbst := e
    for motiveArg in motiveArgs.reverse, discr in discrs.reverse do
      eAbst ← kabstract eAbst discr
      eAbst := eAbst.instantiate1 motiveArg
    -- Up to this point, this is cargo-culted from `CasesOn.App.addArg`
    -- Let's create something Prop-typed that mentions `e`, by writing `e = e`.
    let eEq ← mkEq eAbst eAbst
    let motive ← mkLambdaFVars motiveArgs eEq
    let us := if c.propOnly then c.us else levelZero :: c.us.tail!
    -- Now instantiate the casesOn wth this synthetic motive
    let aux := mkAppN (mkConst c.declName us) c.params
    let aux := mkApp aux motive
    let aux := mkAppN aux discrs
    check aux
    let auxType ← inferType aux
    -- The type of the remaining arguments will mention `e` instantiated for each arg
    -- so extract them
    let (altAuxs, _, _) ← Lean.Meta.forallMetaTelescope auxType
    let altAuxTys ← altAuxs.mapM (inferType ·)
    (Array.zip c.altNumParams altAuxTys).mapM fun (altNumParams, altAuxTy) => do
      let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAuxTy
      unless fvs.size = altNumParams do
        throwError "failed to transfer argument through matcher application, alt type must be telescope with #{altNumParams} arguments"
      -- extract type from our synthetic equality
      let body := body.getArg! 2
      -- and abstract over the parameters of the alternatives, so that we can safely pass the Expr out
      Expr.abstractM body fvs

/-- A non-failing version of `transform` -/
-- PR'ed at https://github.com/leanprover/lean4/pull/2882
def _root_.Lean.Meta.CasesOnApp.transform? (c : CasesOnApp) (e : Expr) :
    MetaM (Option (Array Expr)) :=
  try
    return some (← c.transform e)
  catch _ =>
    return none

-- Q: Is it really not possible to add this to the `where` clause?
@[reducible]
def M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache recFnName) MetaM) β

/--
Traverses the given expression `e`, and invokes the continuation `k`
at every saturated call to `recFnName`.

The expression `scrut` is passed along, and refined when going under a matcher
or `casesOn` application.
-/
partial def withRecApps {α} (recFnName : Name) (fixedPrefixSize : Nat) (scrut : Expr) (e : Expr)
    (k : Expr → Array Expr → MetaM α) : MetaM (Array α) := do
  trace[Elab.definition.wf] "withRecApps: {indentExpr e}"
  let (_, as) ← loop scrut e |>.run #[] |>.run' {}
  return as
where
  processRec (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      loop scrut (← etaExpand e)
    else
      let a ← k scrut e.getAppArgs
      modifyThe (Array α) (·.push a)

  processApp (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    e.withApp fun f args => do
      args.forM (loop scrut)
      if f.isConstOf recFnName then
        processRec scrut e
      else
        loop scrut f

  containsRecFn (e : Expr) : M recFnName α Bool := do
    modifyGetThe (HasConstCache recFnName) (·.contains e)

  loop (scrut : Expr) (e : Expr) : M recFnName α Unit := do
    if !(← containsRecFn e) then
      return
    -- trace[Elab.definition.wf] "loop: {indentExpr scrut}{indentExpr e}"
    match e with
    | Expr.lam n d b c =>
      loop scrut d
      withLocalDecl n c d fun x => do
        loop scrut (b.instantiate1 x)
    | Expr.forallE n d b c =>
      loop scrut d
      withLocalDecl n c d fun x => do
        loop scrut (b.instantiate1 x)
    | Expr.letE n type val body _ =>
      loop scrut type
      loop scrut val
      withLetDecl n type val fun x => do
        loop scrut (body.instantiate1 x)
    | Expr.mdata _d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop scrut b
      else
        loop scrut b
    | Expr.proj _n _i e => loop scrut e
    | Expr.const .. => if e.isConstOf recFnName then processRec scrut e
    | Expr.app .. =>
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp scrut e
        else
          if let some altScruts ← matcherApp.transform? scrut then
            (Array.zip matcherApp.alts (Array.zip matcherApp.altNumParams altScruts)).forM
              fun (alt, altNumParam, altScrut) =>
                lambdaTelescope alt fun xs altBody => do
                  unless altNumParam ≤ xs.size do
                    throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
                  let altScrut := altScrut.instantiateRev xs[:altNumParam]
                  trace[Elab.definition.wf] "MatcherApp.transform result {indentExpr altScrut}"
                  loop altScrut altBody
          else
            processApp scrut e
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp scrut e
        else
          if let some altScruts ← casesOnApp.transform? scrut then
          (Array.zip casesOnApp.alts (Array.zip casesOnApp.altNumParams altScruts)).forM
            fun (alt, altNumParam, altScrut) =>
              lambdaTelescope alt fun xs altBody => do
                unless altNumParam ≤ xs.size do
                  throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
                let altScrut := altScrut.instantiateRev xs[:altNumParam]
                trace[Elab.definition.wf] "CasesOnApp.transform result {indentExpr altScrut}"
                loop altScrut altBody
          else
            processApp scrut e
      | none => processApp scrut e
    | e => do
      let _ ← ensureNoRecFn recFnName e

/--
A `SavedLocalCtxt` captures the state and local context of a `MetaM`, to be continued later.
-/
-- Q: Sensible?
structure SavedLocalCtxt where
  savedLocalContext : LocalContext
  savedLocalInstances : LocalInstances
  savedState : Meta.SavedState

def SavedLocalCtxt.create : MetaM SavedLocalCtxt := do
  let savedLocalContext ← getLCtx
  let savedLocalInstances ← getLocalInstances
  let savedState ← saveState
  return { savedLocalContext, savedLocalInstances, savedState }

def SavedLocalCtxt.run {α} (slc : SavedLocalCtxt) (k : MetaM α) :
    MetaM α := withoutModifyingState $ do
  withLCtx slc.savedLocalContext slc.savedLocalInstances do
    slc.savedState.restore
    k

/-- A `RecCallContext` focuses on a single recursive call in a unary predefinition,
and runs the given action in the context of that call.  -/
structure RecCallContext where
  --- Function index of caller
  caller : Nat
  --- Parameters of caller
  params : Array Expr
  --- Function index of callee
  callee : Nat
  --- Arguments to callee
  args : Array Expr
  ctxt : SavedLocalCtxt

def RecCallContext.create (caller : Nat) (params : Array Expr) (callee : Nat) (args : Array Expr) :
    MetaM RecCallContext := do
  return { caller, params, callee, args, ctxt := (← SavedLocalCtxt.create) }

/-- Given the packed argument of a (possibly) mutual and (possibly) nary call,
return the function index that is called and the arguments individually.

We expect precisely the expressions produced by `packMutual`, with manifest
`PSum.inr`, `PSum.inl` and `PSigma.mk` constructors, and thus take them apart
rather than using projectinos. -/
def unpackArg {m} [Monad m] [MonadError m] (arities : Array Nat) (e : Expr) :
    m (Nat × Array Expr) := do
  -- count PSum injections to find out which function is doing the call
  let mut funidx := 0
  let mut e := e
  while funidx + 1 < arities.size do
    if e.isAppOfArity ``PSum.inr 3 then
      e := e.getArg! 2
      funidx := funidx + 1
    else if e.isAppOfArity ``PSum.inl 3 then
      e := e.getArg! 2
      break
    else
      throwError "Unexpected expression while unpacking mutual argument"

  -- now unpack PSigmas
  let arity := arities[funidx]!
  let mut args := #[]
  while args.size + 1 < arity do
    if e.isAppOfArity ``PSigma.mk 4 then
      args := args.push (e.getArg! 2)
      e := e.getArg! 3
    else
      throwError "Unexpected expression while unpacking n-ary argument"
  args := args.push e
  return (funidx, args)

/-- Traverse a unary PreDefinition, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat) (arities : Array Nat)
    : MetaM (Array RecCallContext) := withoutModifyingState do
  addAsAxiom unaryPreDef
  lambdaTelescope unaryPreDef.value fun xs body => do
    unless xs.size == fixedPrefixSize + 1 do
      -- Maybe cleaner to have lambdaBoundedTelescope?
      throwError "Unexpected number of lambdas in unary pre-definition"
    -- trace[Elab.definition.wf] "collectRecCalls: {xs} {body}"
    let param := xs[fixedPrefixSize]!
    withRecApps unaryPreDef.declName fixedPrefixSize param body fun param args => do
      unless args.size ≥ fixedPrefixSize + 1 do
        throwError "Insufficient arguments in recursive call"
      let arg := args[fixedPrefixSize]!
      let (caller, params) ← unpackArg arities param
      let (callee, args) ← unpackArg arities arg
      RecCallContext.create caller params callee args

inductive GuessLexRel | lt | eq | le | no_idea
deriving Repr, DecidableEq

instance : ToFormat GuessLexRel where
  format | .lt => "<"
         | .eq => "="
         | .le => "≤"
         | .no_idea => "?"

def GuessLexRel.toNatRel : GuessLexRel → Expr
  | lt => mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]
  | eq => mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Nat]
  | le => mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat]
  | no_idea => unreachable! -- TODO: keep it partial or refactor?

def mkSizeOf (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  let lvl ← getLevel ty
  let inst ← synthInstance (mkAppN (mkConst ``SizeOf [lvl]) #[ty])
  let res := mkAppN (mkConst ``sizeOf [lvl]) #[ty,  inst, e]
  check res
  return res

-- For a given recursive call and choice of paramter index,
-- try to prove requality, < or ≤
def evalRecCall (decrTactic? : Option Syntax) (rcc : RecCallContext) (paramIdx argIdx : Nat) :
    MetaM GuessLexRel := do
  rcc.ctxt.run do
    let param := rcc.params[paramIdx]!
    let arg := rcc.args[argIdx]!
    trace[Elab.definition.wf] "inspectRecCall: {rcc.caller} ({param}) → {rcc.callee} ({arg})"
    let arg ← mkSizeOf rcc.args[argIdx]!
    let param ← mkSizeOf rcc.params[paramIdx]!
    for rel in [GuessLexRel.eq, .lt, .le] do
      let goalExpr := mkAppN rel.toNatRel #[arg, param]
      trace[Elab.definition.wf] "Goal (unchecked): {goalExpr}"
      check goalExpr

      let mvar ← mkFreshExprSyntheticOpaqueMVar goalExpr
      let mvarId := mvar.mvarId!
      let mvarId ← mvarId.cleanup
      -- logInfo m!"Remaining goals: {goalsToMessageData [mvarId]}"
      try
        if rel = .eq then
          MVarId.refl mvarId
        else do
          -- Q: Can I enter TermElabM like this? Is this even needed?
          Lean.Elab.Term.TermElabM.run' do
            match decrTactic? with
            | none =>
              let remainingGoals ← Tactic.run mvarId do
                Tactic.evalTactic (← `(tactic| decreasing_tactic))
              remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]
              let _expr ← instantiateMVars mvar
              -- trace[Elab.definition.wf] "Found {repr rel} proof: {expr}"
              pure ()
            | some decrTactic => Term.withoutErrToSorry do
              -- make info from `runTactic` available
              pushInfoTree (.hole mvarId)
              Term.runTactic mvarId decrTactic
              let _expr ← instantiateMVars mvar
              -- trace[Elab.definition.wf] "Found {repr rel} proof: {expr}"
              pure ()
        return rel
      catch _e =>
        -- trace[Elab.definition.wf] "Did not find {repr rel} proof of {goalsToMessageData [mvarId]}"
        continue
    return .no_idea

-- A cache for `evalRecCall`
structure RecCallCache where mk'' ::
  decrTactic? : Option Syntax
  rcc : RecCallContext
  cache : IO.Ref (Array (Array (Option GuessLexRel)))

def RecCallCache.mk (decrTactic? : Option Syntax) (rcc : RecCallContext) :
    BaseIO RecCallCache := do
  let cache ← IO.mkRef <| Array.mkArray rcc.params.size (Array.mkArray rcc.args.size Option.none)
  return { decrTactic?, rcc, cache }

def RecCallCache.eval (rc: RecCallCache) (paramIdx argIdx : Nat) : MetaM GuessLexRel := do
  -- Check the cache first
  if let Option.some res := (← rc.cache.get)[paramIdx]![argIdx]! then
    return res
  else
    let res ← evalRecCall rc.decrTactic? rc.rcc paramIdx argIdx
    rc.cache.modify (·.modify paramIdx (·.set! argIdx res))
    return res

def RecCallCache.pretty (rc : RecCallCache) : IO Format := do
  let mut r := Format.nil
  let d ← rc.cache.get
  for paramIdx in [:d.size] do
    for argIdx in [:d[paramIdx]!.size] do
      if let .some entry := d[paramIdx]![argIdx]! then
        r := r ++
          f!"(Param {paramIdx}, arg {argIdx}): {entry}" ++ Format.line
  return r

/-- The measures that we order lexicographically can be comparing arguments,
or numbering the functions -/
inductive MutualMeasure where
  | args : Array Nat → MutualMeasure
  --- The given function index is assigned 1, the rest 0
  | func : Nat → MutualMeasure

-- Evaluate a call at a given measure
def inspectCall (rc : RecCallCache) : MutualMeasure → MetaM GuessLexRel
  | .args argIdxs => do
    let paramIdx := argIdxs[rc.rcc.caller]!
    let argIdx := argIdxs[rc.rcc.callee]!
    rc.eval paramIdx argIdx
  | .func funIdx => do
    if rc.rcc.caller == funIdx && rc.rcc.callee != funIdx then
      return .lt
    if rc.rcc.caller != funIdx && rc.rcc.callee == funIdx then
      return .no_idea
    else
      return .eq

/--
  Given a predefinition with value `fun (x_₁ ... xₙ) (y_₁ : α₁)... (yₘ : αₘ) => ...`,
  where `n = fixedPrefixSize`, return an array `A` s.t. `i ∈ A` iff `sizeOf yᵢ` reduces to a literal.
  This is the case for types such as `Prop`, `Type u`, etc.
  This arguments should not be considered when guessing a well-founded relation.
  See `generateCombinations?`
-/
def getForbiddenByTrivialSizeOf (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Nat) :=
  lambdaTelescope preDef.value fun xs _ => do
    let mut result := #[]
    for x in xs[fixedPrefixSize:], i in [:xs.size] do
      try
        let sizeOf ← whnfD (← mkAppM ``sizeOf #[x])
        if sizeOf.isLit then
         result := result.push i
      catch _ =>
        result := result.push i
    return result


-- Generate all combination of arguments, skipping those that are forbidden.
-- Sorts the uniform combinations ([0,0,0], [1,1,1]) to the front; they
-- are commonly most useful to try first, when the mutually recursive functions have similar
-- argument structures
partial def generateCombinations? (forbiddenArgs : Array (Array Nat)) (numArgs : Array Nat)
    (threshold : Nat := 32) : Option (Array (Array Nat)) :=
  (do goUniform 0; go 0 #[]) |>.run #[] |>.2
where
  isForbidden (fidx : Nat) (argIdx : Nat) : Bool :=
    if h : fidx < forbiddenArgs.size then
       forbiddenArgs[fidx] |>.contains argIdx
    else
      false

  -- Enumerate all permissible uniform combinations
  goUniform (argIdx : Nat) : OptionT (StateM (Array (Array Nat))) Unit  := do
    if numArgs.all (argIdx < ·) then
      unless forbiddenArgs.any (·.contains argIdx) do
        modify (·.push (Array.mkArray numArgs.size argIdx))
      goUniform (argIdx + 1)

  -- Enumerate all other permissible combinations
  go (fidx : Nat) : OptionT (ReaderT (Array Nat) (StateM (Array (Array Nat)))) Unit := do
    if h : fidx < numArgs.size then
      let n := numArgs[fidx]
      for argIdx in [:n] do
        unless isForbidden fidx argIdx do
          withReader (·.push argIdx) (go (fidx + 1))
    else
      let comb ← read
      unless comb.all (· == comb[0]!) do
        modify (·.push comb)
      if (← get).size > threshold then
        failure


/-- The core logic of guessing the lexicographic order
Given a matrix that for each call and measure indicates whether that measure is
decreasing, equal, less-or-equal or unknown, It finds a sequence of measures
that is lexicographically decreasing.

The matrix is implemented here as an array of monadic query methods only so that
we can fill is lazily. Morally, this is a pure function
-/
partial def solve {m} {α} [Monad m] (measures : Array α)
  (calls : Array (α → m GuessLexRel)) : m (Option (Array α)) := do
  go measures calls #[]
  where
  go (measures : Array α) (calls : Array (α → m GuessLexRel)) (acc : Array α) := do
    if calls.isEmpty then return .some acc

    -- Find the first measure that has at least one < and otherwise only = or <=
    for h : measureIdx in [:measures.size] do
      let measure := measures[measureIdx]'h.2
      let mut has_lt := false
      let mut all_le := true
      let mut todo := #[]
      for call in calls do
        let entry ← call measure
        if entry = .lt then
          has_lt := true
        else
          todo := todo.push call
          if entry != .le && entry != .eq then
            all_le := false
            break
      -- No progress here? Try the next measure
      if not (has_lt && all_le) then continue
      -- We found a suitable measure, remove it from the list (mild optimization)
      let measures' := measures.eraseIdx measureIdx
      return ← go measures' todo (acc.push measure)
    -- None found, we have to give up
    return .none


-- Does this really not yet exist? Should it?
partial def mkTupleSyntax : Array Syntax → MetaM Syntax
  | #[]  => `(())
  | #[e] => return e
  | es   => do
    let e : TSyntax `term := ⟨es[0]!⟩
    let es : Syntax.TSepArray `term "," :=
      ⟨(Syntax.SepArray.ofElems (sep := ",") es[1:]).1⟩
    `(term|($e, $es,*))

def buildTermWF (declNames : Array Name) (varNamess : Array (Array Name))
    (measures : Array MutualMeasure) : MetaM TerminationWF := do
  -- logInfo <| m!"Solution: {solution}"
  let mut termByElements := #[]
  for h : funIdx in [:varNamess.size] do
    let vars := (varNamess[funIdx]'h.2).map mkIdent
    let body ← mkTupleSyntax (← measures.mapM fun
      | .args varIdxs =>
          let v := vars.get! (varIdxs[funIdx]!)
          `(sizeOf $v)
      | .func funIdx' => if funIdx' == funIdx then `(1) else `(0)
      )
    let declName := declNames[funIdx]!

    -- TODO: Can we turn it into user-facing syntax? Maybe for a “try-this” feature?
    trace[Elab.definition.wf] "Using termination {declName}: {vars} => {body}"
    termByElements := termByElements.push
      { ref := .missing -- is this the right function
        declName, vars, body,
        implicit := true -- TODO, what is this?
      }
  return .ext termByElements

end Lean.Elab.WF.GuessLex

namespace Lean.Elab.WF

open Lean.Elab.WF.GuessLex

def guessLex (preDefs : Array PreDefinition)  (unaryPreDef : PreDefinition)
    (fixedPrefixSize : Nat) (decrTactic? : Option Syntax) :
    MetaM TerminationWF := do
  try
    let varNamess ← preDefs.mapM (naryVarNames fixedPrefixSize ·)
    let arities := varNamess.map (·.size)
    trace[Elab.definition.wf] "varNames is: {varNamess}"

    -- Collect all recursive calls and extract their context
    let recCalls ←collectRecCalls unaryPreDef fixedPrefixSize arities
    let rcs ← recCalls.mapM (RecCallCache.mk decrTactic? ·)
    let callMatrix := rcs.map (inspectCall ·)

    let forbiddenArgs ← preDefs.mapM fun preDef =>
      getForbiddenByTrivialSizeOf fixedPrefixSize preDef

    -- Enumerate all meausures.
    -- (With many functions with multiple arguments, this can explode a bit.
    -- We could interleave enumerating measure with early pruning based on the recCalls,
    -- once that becomes a problem. Until then, a use can always use an explicit
    -- `terminating_by` annotatin.)
    let some arg_measures := generateCombinations? forbiddenArgs arities
      | throwError "Too many combinations"

    -- The list of measures, including the measures that order functions.
    -- The function ordering measures should come last
    let measures : Array MutualMeasure :=
      arg_measures.map .args ++ (List.range varNamess.size).toArray.map .func

    match ← liftMetaM <| solve measures callMatrix with
    | .some solution => do
      let wf ← buildTermWF (preDefs.map (·.declName)) varNamess solution
      return wf
    | .none => throwError "Cannot find a decreasing lexicographic order"
  catch _ =>
    -- Hide all errors from guessing lexicographic orderings, as before
    -- TODO: surface unexpected errors, maybe surface detailed explanation like Isabelle
    throwError "failed to prove termination, use `termination_by` to specify a well-founded relation"
