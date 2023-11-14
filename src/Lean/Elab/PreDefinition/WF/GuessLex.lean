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
This module implements heuristics to finding lexicographic termination measures
for well-founded recursion. The goal is to try all lexicographic measures and
find one for which all proof obligations go through with the given or default
`decreasing_by` tatic.

The crucial optimiziation is to look at each argument of each recursive call _once_,
try to prove `<` and (if that fails `≤`), and then look at that table to pick a suitable
measure. The next-crucial optimization is to fill that table lazily.

This way, we run the (likely expensive) tactics as few times as possible, while still being
able to consider a possibly large number of combinations.


In the case of mutual recursion, a single measure is not just one argument position, but
one argument from each recursive function. Enumerating these can lead to a combinatoric explosion,
so we bound the nubmer of measures tried.

In addition to measures derived from `sizeOf x` where `x` is an argument, it also considers
measures that order the functions. This way we can support mutual function definitions where
no arguments decrease from one function to another.

The result of this module is a `TerminationWF`, which is then passed on to `wfRecursion`; this
design is crucial so that whatever we infer in this module could also be written manually by the
user. It would be bad if there are function definitions that can only be processed with the
guessed lexicographic order.

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
def naryVarNames (fixedPrefixSize : Nat) (preDef : PreDefinition) : TermElabM (Array Name):= do
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
  returns the expressions `B[C_1[ys_1]])  ... B[C_n[ys_n]]`.
  (with `ys_i` as loose bound variable, ready to be `.instantiate`d)
  Cf. `MatcherApp.addArg`.
-/
def _root_.Lean.Meta.MatcherApp.transform {m}
    -- TODO: Do we really need all these type classes?
    [MonadControlT MetaM m] [MonadLiftT MetaM m] [Monad m] [MonadOptions m] [MonadTrace m]
    [MonadLiftT IO m] [MonadError m] [AddMessageContext m]
    (matcherApp : MatcherApp) (e : Expr) (k : Expr → Expr → m Unit) : m Unit :=
  lambdaTelescope matcherApp.motive fun motiveArgs _motiveBody => do
    unless motiveArgs.size == matcherApp.discrs.size do
      -- This error can only happen if someone implemented a transformation that rewrites the motive created by `mkMatcher`.
      throwError "unexpected matcher application, motive must be lambda expression with #{matcherApp.discrs.size} arguments"

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
      throwError "failed to add argument to matcher application, type error when constructing the new motive"
    let auxType ← inferType aux
    let (altAuxs, _, _) ← Lean.Meta.forallMetaTelescope auxType
    let altAuxTys ← altAuxs.mapM (inferType ·)
    (Array.zip matcherApp.alts altAuxTys).forM fun (alt, altAuxTy) => do
    let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAuxTy
    trace[Elab.definition.wf] "alt fvs: {fvs}"
    let body := body.getArg! 2
    -- and abstract over the parameters of the alternative again
    let body ← Expr.abstractM body fvs
    -- Go under the lambdas of the alt
    -- (TODO: Use bounded lambdaTelescope)
    lambdaTelescope alt fun xs altBody => do
      let body := body.instantiateRev (xs.extract 0 fvs.size)
      trace[Elab.definition.wf] "CasesOnApp.transform result {indentExpr body}"
      k body altBody

/--
  Given a `casesOn` application `c` of the form
  ```
  casesOn As (fun is x => motive[i, xs]) is major  (fun ys_1 => (alt_1 : motive (C_1[ys_1])) ... (fun ys_n => (alt_n : motive (C_n[ys_n]) remaining
  ```
  and a type `e : B[is, major]`, for every alternative `i`, construct the type
  ```
  B[C_i[ys_i]]
  ```
  (with `ys_i` as loose bound variable, ready to be `.instantiate`d)
-/
def _root_.Lean.Meta.CasesOnApp.transform {m}
  -- TODO: Do we really need all these type classes?
  [MonadControlT MetaM m] [MonadLiftT MetaM m] [Monad m] [MonadOptions m] [MonadTrace m]
  [MonadLiftT IO m] [MonadError m] [AddMessageContext m]
    (c : CasesOnApp) (e : Expr) (k : Expr → Expr → m Unit) : m Unit :=
  lambdaTelescope c.motive fun motiveArgs _motiveBody => do
    unless motiveArgs.size == c.indices.size + 1 do
      throwError "failed to add argument to `casesOn` application, motive must be lambda expression with #{c.indices.size + 1} binders"
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
    (Array.zip c.alts altAuxTys).forM fun (alt, altAuxTy) => do
      let (fvs, _, body) ← Lean.Meta.forallMetaTelescope altAuxTy
      trace[Elab.definition.wf] "alt fvs: {fvs}"
      let body := body.getArg! 2
      -- and abstract over the parameters of the alternative again
      let body ← Expr.abstractM body fvs
      -- Go under the lambdas of the alt
      -- (TODO: Use bounded lambdaTelescope)
      lambdaTelescope alt fun xs altBody => do
        let body := body.instantiateRev (xs.extract 0 fvs.size)
        trace[Elab.definition.wf] "CasesOnApp.transform result {indentExpr body}"
        k body altBody

@[reducible]
def M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache recFnName) TermElabM) β

partial def withRecApps {α} (recFnName : Name) (fixedPrefixSize : Nat) (e : Expr) (scrut : Expr)
    (k : Expr → Array Expr → TermElabM α) : TermElabM (Array α) := do
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
          matcherApp.transform scrut fun scrut' altBody => do
            loop scrut' altBody
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp scrut e
        else
          casesOnApp.transform scrut fun scrut' altBody => do
            loop scrut' altBody
      | none => processApp scrut e
    | e => do
      let _ ← ensureNoRecFn recFnName e

/-- A `SavedLocalCtxt` captures the local context (e.g. of a recursive call),
so that it can be resumed later.
-/
structure SavedLocalCtxt where
  savedState : Term.SavedState
  savedLocalContext : LocalContext
  savedLocalInstances : LocalInstances
  savedTermContext : Term.Context

def SavedLocalCtxt.create : TermElabM SavedLocalCtxt := do
  let savedState ← saveState
  let savedLocalContext ← getLCtx
  let savedLocalInstances ← getLocalInstances
  let savedTermContext ← readThe Term.Context
  return { savedState, savedLocalContext, savedLocalInstances, savedTermContext }


def SavedLocalCtxt.run {α} (slc : SavedLocalCtxt) (k : TermElabM α) :
    TermElabM α := withoutModifyingState $ do
  restoreState slc.savedState
  withLCtx slc.savedLocalContext slc.savedLocalInstances do
  withTheReader Term.Context (fun _ => slc.savedTermContext) do
  k

def SavedLocalCtxt.within {α} (slc : SavedLocalCtxt) (k : TermElabM α) :
    TermElabM (SavedLocalCtxt × α) :=
  slc.run do
    let x ← k
    let slc' ← SavedLocalCtxt.create
    pure (slc', x)


/-- A `RecCallContext` focuses on a single recursive call in a unary predefinition,
and runs the given action in the context of that call.
-/
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

/-- Given the packed argument of a (possibly) mutual and (possibly) nary call,
return the function index that is called and the arguments individually.
Cf. `packMutual`
-/
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

def RecCallContext.create (caller : Nat) (params : Array Expr) (callee : Nat) (args : Array Expr) :
    TermElabM RecCallContext := do
  return { caller, params, callee, args, ctxt := (← SavedLocalCtxt.create) }

/-- Traverse a unary PreDefinition, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat) (arities : Array Nat)
    : TermElabM (Array RecCallContext) := withoutModifyingState do
  addAsAxiom unaryPreDef
  lambdaTelescope unaryPreDef.value fun xs body => do
    unless xs.size == fixedPrefixSize + 1 do
      -- Maybe cleaner to have lambdaBoundedTelescope?
      throwError "Unexpected number of lambdas in unary pre-definition"
    -- trace[Elab.definition.wf] "collectRecCalls: {xs} {body}"
    let param := xs[fixedPrefixSize]!
    withRecApps unaryPreDef.declName fixedPrefixSize body param fun param args => do
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

def mkSizeOf (e : Expr) : TermElabM Expr := do
  let ty ← inferType e
  let lvl ← getLevel ty
  let inst ← synthInstance (mkAppN (mkConst ``SizeOf [lvl]) #[ty])
  let res := mkAppN (mkConst ``sizeOf [lvl]) #[ty,  inst, e]
  check res
  return res

-- For a given recursive call and choice of paramter index,
-- try to prove requality, < or ≤
def evalRecCall (decrTactic? : Option Syntax) (rcc : RecCallContext) (paramIdx argIdx : Nat) :
    TermElabM GuessLexRel := do
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

def RecCallCache.eval (rc: RecCallCache) (paramIdx argIdx : Nat) :
    TermElabM GuessLexRel := do
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
def inspectCall (rc : RecCallCache) : MutualMeasure → TermElabM GuessLexRel
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

def buildTermWF (declNames : Array Name) (varNamess : Array (Array Name))
    (measures : Array MutualMeasure) : TermElabM TerminationWF := do
  -- logInfo <| m!"Solution: {solution}"
  let mut termByElements := #[]
  for h : funIdx in [:varNamess.size] do
    let vars := (varNamess[funIdx]'h.2).map mkIdent
    let body := ← Lean.Elab.Term.Quotation.mkTuple (← measures.mapM fun
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
    (fixedPrefixSize : Nat )(decrTactic? : Option Syntax) :
    TermElabM TerminationWF := do
  let varNamess ← preDefs.mapM (naryVarNames fixedPrefixSize)
  let arities := varNamess.map (·.size)
  trace[Elab.definition.wf] "varNames is: {varNamess}"

  -- Collect all recursive calls and extract their context
  let recCalls ← collectRecCalls unaryPreDef fixedPrefixSize arities
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

  match ← solve measures callMatrix with
  | .some solution =>
     buildTermWF (preDefs.map (·.declName)) varNamess solution
  | .none =>
    throwError "failed to prove termination, use `termination_by` to specify a well-founded relation"
