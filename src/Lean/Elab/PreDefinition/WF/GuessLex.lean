/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Util.HasConstCache
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Refl
import Lean.Meta.Tactic.TryThis
import Lean.Meta.ArgsPacker
import Lean.Elab.Quotation
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Mutual
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.TerminationMeasure
import Lean.Elab.PreDefinition.FixedParams
import Lean.Elab.PreDefinition.WF.Basic
import Lean.Data.Array


/-!
This module finds lexicographic termination measures for well-founded recursion.

Starting with basic measures (`sizeOf xᵢ` for all parameters `xᵢ`), and complex measures
(e.g. `e₂ - e₁` if `e₁ < e₂` is found in the context of a recursive call) it tries all combinations
until it finds one where all proof obligations go through with the given tactic (`decerasing_by`),
if given, or the default `decreasing_tactic`.

For mutual recursion, a single measure is not just one parameter, but one from each recursive
function. Enumerating these can lead to a combinatoric explosion, so we bound
the number of measures tried.

In addition to measures derived from `sizeOf xᵢ`, it also considers measures
that assign an order to the functions themselves. This way we can support mutual
function definitions where no arguments decrease from one function to another.

The result of this module is a `TerminationWF`, which is then passed on to `wfRecursion`; this
design is crucial so that whatever we infer in this module could also be written manually by the
user. It would be bad if there are function definitions that can only be processed with the
guessed lexicographic order.

The following optimizations are applied to make this feasible:

1. The crucial optimization is to look at each measure of each recursive call
   _once_, try to prove `<` and (if that fails `≤`), and then look at that table to
   pick a suitable measure.

2. The next-crucial optimization is to fill that table lazily.  This way, we run the (likely
   expensive) tactics as few times as possible, while still being able to consider a possibly
   large number of combinations.

3. Before we even try to prove `<`, we check if the measures are equal (`=`). No well-founded
   measure will relate equal terms, likely this check is faster than firing up the tactic engine,
   and it adds more signal to the output.

4. Instead of traversing the whole function body over and over, we traverse it once and store
   the arguments (in unpacked form) and the local `MetaM` state at each recursive call
   (see `collectRecCalls`), which we then re-use for the possibly many proof attempts.

The logic here is based on “Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL”
by Lukas Bulwahn, Alexander Krauss, and Tobias Nipkow, 10.1007/978-3-540-74591-4_5
<https://www21.in.tum.de/~nipkow/pubs/tphols07.pdf>.

We got the idea of considering the measure `e₂ - e₁` if we see `e₁ < e₂` from
“Termination Analysis with Calling Context Graphs” by Panagiotis Manolios &
Daron Vroon, https://doi.org/10.1007/11817963_36.
-/

set_option autoImplicit false

open Lean Meta Elab

namespace Lean.Elab.WF.GuessLex

register_builtin_option showInferredTerminationBy : Bool := {
  defValue := false
  descr    := "In recursive definitions, show the inferred `termination_by` measure."
}


/--
Given a predefinition, return the variable names in the outermost lambdas.
Includes the “fixed prefix”.

The length of the returned array is also used to determine the arity
of the function, so it should match what `packDomain` does.
-/
def originalVarNames (preDef : PreDefinition) : MetaM (Array Name) := do
  lambdaTelescope preDef.value fun xs _ => xs.mapM (·.fvarId!.getUserName)

/--
Given the original parameter names from `originalVarNames`, find
good variable names to be used when talking about termination measures:
Use user-given parameter names if present; use x1...xn otherwise.

The names ought to accessible (no macro scopes) and fresh wrt to the current environment,
so that with `showInferredTerminationBy` we can print them to the user reliably.
We do that by appending `'` as needed.

It is possible (but unlikely without malice) that some of the user-given names
shadow each other, and the guessed relation refers to the wrong one. In that
case, the user gets to keep both pieces (and may have to rename variables).
-/
partial
def naryVarNames (xs : Array Name) : MetaM (Array Name) := do
  let mut ns : Array Name := #[]
  for h : i in [:xs.size] do
    let n := xs[i]
    let n ← if n.hasMacroScopes then
        freshen ns (.mkSimple s!"x{i+1}")
      else
        pure n
    ns := ns.push n
  return ns
  where
    freshen  (ns : Array Name) (n : Name): MetaM Name := do
      if !(ns.elem n) && (← resolveGlobalName n).isEmpty then
        return n
      else
        freshen ns (n.appendAfter "'")

/-- A termination measure with extra fields for use within GuessLex -/
structure BasicMeasure extends TerminationMeasure where
  /--
  Like `.fn`, but unconditionally with `sizeOf` at the right type.
  We use this one when in `evalRecCall`
  -/
  natFn : Expr
deriving Inhabited

/-- String description of this measure -/
def BasicMeasure.toString (measure : BasicMeasure) : MetaM String := do
  lambdaTelescope measure.fn fun _xs e => do
    -- This is a bit slopping if `measure.fn` takes more parameters than the `PreDefinition`
    return (← ppExpr e).pretty

/--
Determine if the measure for parameter `x` should be `sizeOf x` or just `x`.

For non-mutual definitions, we omit `sizeOf` when the measure does not depend on
the other varying parameters, and its `WellFoundedRelation` instance goes via `SizeOf`.

For mutual definitions, we omit `sizeOf` only when the measure is (at reducible transparency!) of
type `Nat` (else we'd have to worry about differently-typed measures from different functions to
line up).
-/
def mayOmitSizeOf (is_mutual : Bool) (args : Array Expr) (x : Expr) : MetaM Bool := do
  let t ← inferType x
  if is_mutual
  then
    withReducible (isDefEq t (.const `Nat []))
  else
    try
      if t.hasAnyFVar (fun fvar => args.contains (.fvar fvar)) then
        pure false
      else
        let u ← getLevel t
        let wfi ← synthInstance (.app (.const ``WellFoundedRelation [u]) t)
        let soi ← synthInstance (.app (.const ``SizeOf [u]) t)
        isDefEq wfi (mkApp2 (.const ``sizeOfWFRel [u]) t soi)
    catch _ =>
      pure false

/-- Sets the user names for the given freevars in `xs`. -/
def withUserNames {α} (xs : Array Expr) (ns : Array Name) (k : MetaM α) : MetaM α := do
  let mut lctx ←  getLCtx
  for x in xs, n in ns do lctx := lctx.setUserName x.fvarId! n
  withLCtx' lctx k

/-- Create one measure for each (eligible) parameter of the given predefintion.  -/
def simpleMeasures (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms)
    (userVarNamess : Array (Array Name)) : MetaM (Array (Array BasicMeasure)) := do
  let is_mutual : Bool := preDefs.size > 1
  preDefs.mapIdxM fun funIdx preDef => do
    lambdaTelescope preDef.value fun params _ => do
      let xs := fixedParamPerms.perms[funIdx]!.pickVarying params
      withUserNames xs userVarNamess[funIdx]! do
        let mut ret : Array BasicMeasure := #[]
        for x in xs do
          -- If the `SizeOf` instance produces a constant (e.g. because it's type is a `Prop` or
          -- `Type`), then ignore this parameter
          let sizeOf ← whnfD (← mkAppM ``sizeOf #[x])
          if sizeOf.isLit then continue

          let natFn ← mkLambdaFVars params (← mkAppM ``sizeOf #[x])
          -- Determine if we need to exclude `sizeOf` in the measure we show/pass on.
          let fn ←
            if  ← mayOmitSizeOf is_mutual xs x
            then mkLambdaFVars params x
            else pure natFn
          ret := ret.push { ref := .missing, structural := false, fn, natFn }
        return ret

/-- Internal monad used by `withRecApps` -/
abbrev M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache #[recFnName]) MetaM) β

/--
Traverses the given expression `e`, and invokes the continuation `k`
at every saturated call to `recFnName`.

The expression `param` is passed along, and refined when going under a matcher
or `casesOn` application.
-/
partial def withRecApps {α} (recFnName : Name) (fixedPrefixSize : Nat) (param : Expr) (e : Expr)
    (k : Expr → Array Expr → MetaM α) : MetaM (Array α) := do
  trace[Elab.definition.wf] "withRecApps (param {param}): {indentExpr e}"
  let (_, as) ← loop param e |>.run #[] |>.run' {}
  return as
where
  processRec (param : Expr) (e : Expr) : M recFnName α Unit := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      loop param (← etaExpand e)
    else
      let a ← k param e.getAppArgs
      modifyThe (Array α) (·.push a)

  processApp (param : Expr) (e : Expr) : M recFnName α Unit := do
    e.withApp fun f args => do
      args.forM (loop param)
      if f.isConstOf recFnName then
        processRec param e
      else
        loop param f

  containsRecFn (e : Expr) : M recFnName α Bool := do
    modifyGetThe (HasConstCache #[recFnName]) (·.contains e)

  loop (param : Expr) (e : Expr) : M recFnName α Unit := do
    if !(← containsRecFn e) then
      return
    match e with
    | Expr.lam n d b c =>
      loop param d
      withLocalDecl n c d fun x => do
        loop param (b.instantiate1 x)
    | Expr.forallE n d b c =>
      loop param d
      withLocalDecl n c d fun x => do
        loop param (b.instantiate1 x)
    | Expr.letE n type val body _ =>
      loop param type
      loop param val
      withLetDecl n type val fun x => do
        loop param (body.instantiate1 x)
    | Expr.mdata _d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop param b
      else
        loop param b
    | Expr.proj _n _i e => loop param e
    | Expr.const .. => if e.isConstOf recFnName then processRec param e
    | Expr.app .. =>
      match (← matchMatcherApp? (alsoCasesOn := true) e) with
      | some matcherApp =>
        if let some altParams ← matcherApp.refineThrough? param then
          matcherApp.discrs.forM (loop param)
          (Array.zip matcherApp.alts (Array.zip matcherApp.altNumParams altParams)).forM
            fun (alt, altNumParam, altParam) =>
              lambdaBoundedTelescope altParam altNumParam fun xs altParam => do
                unless altNumParam = xs.size do
                  throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
                let altBody := alt.beta xs
                loop altParam altBody
          matcherApp.remaining.forM (loop param)
        else
          processApp param e
      | none => processApp param e
    | e => do
      ensureNoRecFn #[recFnName] e

/--
A `SavedLocalContext` captures the state and local context of a `MetaM`, to be continued later.
-/
structure SavedLocalContext where
  savedLocalContext : LocalContext
  savedLocalInstances : LocalInstances
  savedState : Meta.SavedState

/-- Capture the `MetaM` state including local context. -/
def SavedLocalContext.create : MetaM SavedLocalContext := do
  let savedLocalContext ← getLCtx
  let savedLocalInstances ← getLocalInstances
  let savedState ← saveState
  return { savedLocalContext, savedLocalInstances, savedState }

/-- Run a `MetaM` action in the saved state. -/
def SavedLocalContext.run {α} (slc : SavedLocalContext) (k : MetaM α) :
    MetaM α :=
  withoutModifyingState $ do
    withLCtx slc.savedLocalContext slc.savedLocalInstances do
      slc.savedState.restore
      k

/-- A `RecCallWithContext` focuses on a single recursive call in a unary predefinition,
and runs the given action in the context of that call.  -/
structure RecCallWithContext where
  /-- Syntax location of recursive call -/
  ref : Syntax
  /-- Function index of caller -/
  caller : Nat
  /-- Parameters of caller (including fixed prefix) -/
  params : Array Expr
  /-- Function index of callee -/
  callee : Nat
  /-- Arguments to callee (including fixed prefix) -/
  args : Array Expr
  ctxt : SavedLocalContext

/-- Store the current recursive call and its context. -/
def RecCallWithContext.create (ref : Syntax) (caller : Nat) (params : Array Expr) (callee : Nat)
    (args : Array Expr) : MetaM RecCallWithContext := do
  return { ref, caller, params, callee, args, ctxt := (← SavedLocalContext.create) }


/--
The elaborator is prone to duplicate terms, including recursive calls, even if the user
only wrote a single one. This duplication is wasteful if we run the tactics on duplicated
calls, and confusing in the output of GuessLex. So prune the list of recursive calls,
and remove those where another call exists that has the same goal and context that is no more
specific.
-/
def filterSubsumed (rcs : Array RecCallWithContext ) : Array RecCallWithContext := Id.run do
  rcs.filterPairsM fun rci rcj => do
    if rci.caller == rcj.caller && rci.callee == rcj.callee &&
      rci.params == rcj.params && rci.args == rcj.args then
      -- same goals; check contexts.
        let lci := rci.ctxt.savedLocalContext
        let lcj := rcj.ctxt.savedLocalContext
        if lci.isSubPrefixOf lcj then
          -- rci is better
          return (true, false)
        else if lcj.isSubPrefixOf lci then
          -- rcj is better
          return (false, true)
    return (true, true)

/--
Traverse a unary `PreDefinition`, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedParamPerms : FixedParamPerms)
    (argsPacker : ArgsPacker) : MetaM (Array RecCallWithContext) := withoutModifyingState do
  addAsAxiom unaryPreDef
  lambdaBoundedTelescope unaryPreDef.value (fixedParamPerms.numFixed + 1) fun xs body => do
    unless xs.size == fixedParamPerms.numFixed + 1 do
      throwError "Unexpected number of lambdas in unary pre-definition"
    let ys := xs[:fixedParamPerms.numFixed]
    let param := xs[fixedParamPerms.numFixed]!
    withRecApps unaryPreDef.declName fixedParamPerms.numFixed param body fun param args => do
      unless args.size ≥ fixedParamPerms.numFixed + 1 do
        throwError "Insufficient arguments in recursive call"
      let arg := args[fixedParamPerms.numFixed]!
      trace[Elab.definition.wf] "collectRecCalls: {unaryPreDef.declName} ({param}) → {unaryPreDef.declName} ({arg})"
      let some (caller, params) := argsPacker.unpack param
        | throwError "Cannot unpack param, unexpected expression:{indentExpr param}"
      let some (callee, args) := argsPacker.unpack arg
        | throwError "Cannot unpack arg, unexpected expression:{indentExpr arg}"
      let callerParams := fixedParamPerms.perms[caller]!.buildArgs ys params
      let calleeArgs := fixedParamPerms.perms[callee]!.buildArgs ys args
      RecCallWithContext.create (← getRef) caller callerParams callee calleeArgs

/-- Is the expression a `<`-like comparison of `Nat` expressions -/
def isNatCmp (e : Expr) : Option (Expr × Expr) :=
  match_expr e with
  | LT.lt α _ e₁ e₂ => if α.isConstOf ``Nat then some (e₁, e₂) else none
  | LE.le α _ e₁ e₂ => if α.isConstOf ``Nat then some (e₁, e₂) else none
  | GT.gt α _ e₁ e₂ => if α.isConstOf ``Nat then some (e₂, e₁) else none
  | GE.ge α _ e₁ e₂ => if α.isConstOf ``Nat then some (e₂, e₁) else none
  | _ => none

def complexMeasures (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms)
    (userVarNamess : Array (Array Name)) (recCalls : Array RecCallWithContext) :
    MetaM (Array (Array BasicMeasure)) := do
  preDefs.mapIdxM fun funIdx _preDef => do
    let mut measures := #[]
    for rc in recCalls do
      -- Only look at calls from the current function
      unless rc.caller = funIdx do continue
      -- Only look at calls where the parameters have not been refined
      unless rc.params.all (·.isFVar) do continue
      let varyingParams := fixedParamPerms.perms[funIdx]!.pickVarying rc.params
      let varyingFVars := varyingParams.map (·.fvarId!)
      let params := rc.params.map (·.fvarId!)
      measures ← rc.ctxt.run do
        withUserNames varyingParams userVarNamess[funIdx]! do
        trace[Elab.definition.wf] "rc: {rc.caller} ({rc.params}) → {rc.callee} ({rc.args})"
        let mut measures := measures
        for ldecl in ← getLCtx do
          if let some (e₁, e₂) := isNatCmp ldecl.type then
            -- We only want to consider these expressions if they depend only on the function's
            -- immediate arguments, so check that
            if e₁.hasAnyFVar (! params.contains ·) then continue
            if e₂.hasAnyFVar (! params.contains ·) then continue
            -- If e₁ does not depend on any varying parameters, simply ignore it
            let e₁_is_const := ! e₁.hasAnyFVar (varyingFVars.contains ·)
            let body := if e₁_is_const then e₂ else mkNatSub e₂ e₁
            -- Avoid adding simple measures
            unless body.isFVar do
              let fn ← mkLambdaFVars rc.params body
              -- Avoid duplicates
              unless ← measures.anyM (isDefEq ·.fn fn) do
                measures := measures.push { ref := .missing, structural := false,  fn, natFn := fn }
        return measures
    return measures

/-- A `GuessLexRel` described how a recursive call affects a measure; whether it
decreases strictly, non-strictly, is equal, or else.  -/
inductive GuessLexRel | lt | eq | le | no_idea
deriving Repr, DecidableEq

instance : ToString GuessLexRel where
  toString | .lt => "<"
           | .eq => "="
           | .le => "≤"
           | .no_idea => "?"

instance : ToFormat GuessLexRel where
  format r := toString r

/-- Given a `GuessLexRel`, produce a binary `Expr` that relates two `Nat` values accordingly. -/
def GuessLexRel.toNatRel : GuessLexRel → Expr
  | lt => mkAppN (mkConst ``LT.lt [levelZero]) #[mkConst ``Nat, mkConst ``instLTNat]
  | eq => mkAppN (mkConst ``Eq [levelOne]) #[mkConst ``Nat]
  | le => mkAppN (mkConst ``LE.le [levelZero]) #[mkConst ``Nat, mkConst ``instLENat]
  | no_idea => unreachable!

/--
For a given recursive call, and a choice of parameter and argument index,
try to prove equality, < or ≤.
-/
def evalRecCall (callerName: Name) (decrTactic? : Option DecreasingBy) (callerMeasures calleeMeasures : Array BasicMeasure)
  (rcc : RecCallWithContext) (callerMeasureIdx calleeMeasureIdx : Nat) : MetaM GuessLexRel := do
  rcc.ctxt.run do
    let callerMeasure := callerMeasures[callerMeasureIdx]!
    let calleeMeasure := calleeMeasures[calleeMeasureIdx]!
    let param := callerMeasure.natFn.beta rcc.params
    let arg := calleeMeasure.natFn.beta rcc.args
    trace[Elab.definition.wf] "inspectRecCall: {rcc.caller} ({param}) → {rcc.callee} ({arg})"
    for rel in [GuessLexRel.eq, .lt, .le] do
      let goalExpr := mkAppN rel.toNatRel #[arg, param]
      trace[Elab.definition.wf] "Goal for {rel}: {goalExpr}"
      check goalExpr

      let mvar ← mkFreshExprSyntheticOpaqueMVar goalExpr
      let mvarId := mvar.mvarId!
      let mvarId ← mvarId.cleanup
      try
        if rel = .eq then
          MVarId.refl mvarId
        else do
          Lean.Elab.Term.TermElabM.run' do Term.withDeclName callerName do
            Term.withoutErrToSorry do
              let remainingGoals ← Tactic.run mvarId do Tactic.withoutRecover do
                applyCleanWfTactic
                let tacticStx : Syntax ←
                  match decrTactic? with
                  | none => pure (← `(tactic| decreasing_tactic)).raw
                  | some decrTactic =>
                    trace[Elab.definition.wf] "Using tactic {decrTactic.tactic.raw}"
                    pure decrTactic.tactic.raw
                Tactic.evalTactic tacticStx
              remainingGoals.forM fun _ => throwError "goal not solved"
        trace[Elab.definition.wf] "inspectRecCall: success!"
        return rel
      catch e =>
        trace[Elab.definition.wf] "Did not find {rel} proof. Goal:{goalsToMessageData [mvarId]}\nError:{indentD e.toMessageData}"
        continue
    return .no_idea

/- A cache for `evalRecCall` -/
structure RecCallCache where mk'' ::
  callerName : Name
  decrTactic? : Option DecreasingBy
  callerMeasures : Array BasicMeasure
  calleeMeasures : Array BasicMeasure
  rcc : RecCallWithContext
  cache : IO.Ref (Array (Array (Option GuessLexRel)))

/-- Create a cache to memoize calls to `evalRecCall descTactic? rcc` -/
def RecCallCache.mk (funNames : Array Name) (decrTactics : Array (Option DecreasingBy)) (measuress : Array (Array BasicMeasure))
    (rcc : RecCallWithContext) :
    BaseIO RecCallCache := do
  let callerName := funNames[rcc.caller]!
  let decrTactic? := decrTactics[rcc.caller]!
  let callerMeasures := measuress[rcc.caller]!
  let calleeMeasures := measuress[rcc.callee]!
  let cache ← IO.mkRef <| Array.mkArray callerMeasures.size (Array.mkArray calleeMeasures.size Option.none)
  return { callerName, decrTactic?, callerMeasures, calleeMeasures, rcc, cache }

/-- Run `evalRecCall` and cache there result -/
def RecCallCache.eval (rc: RecCallCache) (callerMeasureIdx calleeMeasureIdx : Nat) : MetaM GuessLexRel := do
  -- Check the cache first
  if let Option.some res := (← rc.cache.get)[callerMeasureIdx]![calleeMeasureIdx]! then
    return res
  else
    let res ← evalRecCall  rc.callerName rc.decrTactic? rc.callerMeasures rc.calleeMeasures rc.rcc callerMeasureIdx calleeMeasureIdx
    rc.cache.modify (·.modify callerMeasureIdx (·.set! calleeMeasureIdx res))
    return res

/-- Print a single cache entry as a string, without forcing it -/
def RecCallCache.prettyEntry (rcc : RecCallCache) (callerMeasureIdx calleeMeasureIdx : Nat) : MetaM String := do
  let cachedEntries ← rcc.cache.get
  return match cachedEntries[callerMeasureIdx]![calleeMeasureIdx]! with
  | .some rel => toString rel
  | .none => "_"

/-- The measures that we order lexicographically can be comparing basic measures,
or numbering the functions -/
inductive MutualMeasure where
  /-- For every function, the given argument index -/
  | args : Array Nat → MutualMeasure
  /-- The given function index is assigned 1, the rest 0 -/
  | func : Nat → MutualMeasure

/-- Evaluate a recursive call at a given `MutualMeasure` -/
def inspectCall (rc : RecCallCache) : MutualMeasure → MetaM GuessLexRel
  | .args tmIdxs => do
    let callerMeasureIdx := tmIdxs[rc.rcc.caller]!
    let calleeMeasureIdx := tmIdxs[rc.rcc.callee]!
    rc.eval callerMeasureIdx calleeMeasureIdx
  | .func funIdx => do
    if rc.rcc.caller == funIdx && rc.rcc.callee != funIdx then
      return .lt
    if rc.rcc.caller != funIdx && rc.rcc.callee == funIdx then
      return .no_idea
    else
      return .eq


/--
Generate all combination of measures. Assumes we have numbered the measures of each function,
and their counts is in `numMeasures`.

This puts the uniform combinations ([0,0,0], [1,1,1]) to the front; they are commonly most useful to
try first, when the mutually recursive functions have similar argument structures
-/
partial def generateCombinations? (numMeasures : Array Nat) (threshold : Nat := 32) :
    Option (Array (Array Nat)) :=
  (do goUniform 0; go 0 #[]) |>.run #[] |>.2
where
  -- Enumerate all permissible uniform combinations
  goUniform (idx : Nat) : OptionT (StateM (Array (Array Nat))) Unit  := do
    if numMeasures.all (idx < ·) then
      modify (·.push (Array.mkArray numMeasures.size idx))
      goUniform (idx + 1)

  -- Enumerate all other permissible combinations
  go (fidx : Nat) : OptionT (ReaderT (Array Nat) (StateM (Array (Array Nat)))) Unit := do
    if h : fidx < numMeasures.size then
      let n := numMeasures[fidx]
      for idx in [:n] do withReader (·.push idx) (go (fidx + 1))
    else
      let comb ← read
      unless comb.all (· == comb[0]!) do
        modify (·.push comb)
      if (← get).size > threshold then
        failure

/--
Enumerate all measures we want to try.

All measures (resp. combinations thereof) and
possible orderings of functions (if more than one)
-/
def generateMeasures (numMeasures : Array Nat) : MetaM (Array MutualMeasure) := do
  let some arg_measures := generateCombinations? numMeasures
      | throwError "Too many combinations"

  let func_measures :=
    if numMeasures.size > 1 then
      (List.range numMeasures.size).toArray
    else
      #[]

  return arg_measures.map .args ++ func_measures.map .func

/--
The core logic of guessing the lexicographic order
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
      let measure := measures[measureIdx]
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
      if !(has_lt && all_le) then continue
      -- We found a suitable measure, remove it from the list (mild optimization)
      let measures' := measures.eraseIdx measureIdx
      return ← go measures' todo (acc.push measure)
    -- None found, we have to give up
    return .none

/--
Given a matrix (row-major) of strings, arranges them in tabular form.
First column is left-aligned, others right-aligned.
Single space as column separator.
-/
def formatTable : Array (Array String) → String := fun xss => Id.run do
  let mut colWidths := xss[0]!.map (fun _ => 0)
  for hi : i in [:xss.size] do
    for hj : j in [:xss[i].size] do
      if xss[i][j].length > colWidths[j]! then
        colWidths := colWidths.set! j xss[i][j].length
  let mut str := ""
  for hi : i in [:xss.size] do
    for hj : j in [:xss[i].size] do
      let s := xss[i][j]
      if j > 0 then -- right-align
        for _ in [:colWidths[j]! - s.length] do
          str := str ++ " "
      str := str ++ s
      if j = 0 then -- left-align
        for _ in [:colWidths[j]! - s.length] do
          str := str ++ " "
      if j + 1 < xss[i].size then
        str := str ++ " "
    if i + 1 < xss.size then
      str := str ++ "\n"
  return str

/-- Concise textual representation of the source location of a recursive call  -/
def RecCallWithContext.posString (rcc : RecCallWithContext) : MetaM String := do
  let fileMap ← getFileMap
  let .some pos := rcc.ref.getPos? | return ""
  let position := fileMap.toPosition pos
  let endPosStr := match rcc.ref.getTailPos? with
  | some endPos =>
    let endPosition := fileMap.toPosition endPos
    if endPosition.line = position.line then
      s!"-{endPosition.column}"
    else
      s!"-{endPosition.line}:{endPosition.column}"
  | none        => ""
  return s!"{position.line}:{position.column}{endPosStr}"


/-- How to present the basic measure in the table header, possibly abbreviated. -/
def measureHeader (measure : BasicMeasure) : StateT (Nat × String) MetaM String := do
  let s ← measure.toString
  if s.length > 5 then
    let (i, footer) ← get
    let i := i + 1
    let footer := footer ++ s!"#{i}: {s}\n"
    set (i, footer)
    pure s!"#{i}"
  else
    pure s

def collectHeaders {α} (a : StateT (Nat × String) MetaM α) : MetaM (α × String) := do
  let (x, (_, footer)) ← a.run (0, "")
  pure (x,footer)


/-- Explain what we found out about the recursive calls (non-mutual case) -/
def explainNonMutualFailure (measures : Array BasicMeasure) (rcs : Array RecCallCache) : MetaM Format := do
  let (header, footer) ← collectHeaders (measures.mapM measureHeader)
  let mut table : Array (Array String) := #[#[""] ++ header]
  for i in [:rcs.size], rc in rcs do
    let mut row := #[s!"{i+1}) {← rc.rcc.posString}"]
    for argIdx in [:measures.size] do
      row := row.push (← rc.prettyEntry argIdx argIdx)
    table := table.push row
  let out := formatTable table
  if footer.isEmpty then
    return out
  else
    return out ++ "\n\n" ++ footer

/-- Explain what we found out about the recursive calls (mutual case) -/
def explainMutualFailure (declNames : Array Name) (measuress : Array (Array BasicMeasure))
    (rcs : Array RecCallCache) : MetaM Format := do
  let (headerss, footer) ← collectHeaders (measuress.mapM (·.mapM measureHeader))

  let mut r := Format.nil

  for rc in rcs do
    let caller := rc.rcc.caller
    let callee := rc.rcc.callee
    r := r ++ f!"Call from {declNames[caller]!} to {declNames[callee]!} " ++
      f!"at {← rc.rcc.posString}:\n"

    let mut table : Array (Array String) := #[#[""] ++ headerss[caller]!]
    if caller = callee then
      -- For self-calls, only the diagonal is interesting, so put it into one row
      let mut row := #[""]
      for argIdx in [:measuress[caller]!.size] do
        row := row.push (← rc.prettyEntry argIdx argIdx)
      table := table.push row
    else
      for argIdx in [:measuress[callee]!.size] do
        let mut row := #[]
        row := row.push headerss[callee]![argIdx]!
        for paramIdx in [:measuress[caller]!.size] do
          row := row.push (← rc.prettyEntry paramIdx argIdx)
        table := table.push row
    r := r ++ formatTable table ++ "\n"

  unless footer.isEmpty do
    r := r ++ "\n\n" ++ footer

  return r

def explainFailure (declNames : Array Name) (measuress : Array (Array BasicMeasure))
    (rcs : Array RecCallCache) : MetaM Format := do
  let mut r : Format := "The basic measures relate at each recursive call as follows:\n" ++
    "(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)\n"
  if declNames.size = 1 then
    r := r ++ (← explainNonMutualFailure measuress[0]! rcs)
  else
    r := r ++ (← explainMutualFailure declNames measuress rcs)
  return r

/--
For `#[x₁, .., xₙ]` create `(x₁, .., xₙ)`.
-/
def mkProdElem (xs : Array Expr) : MetaM Expr := do
  match xs.size with
  | 0 => return default
  | 1 => return xs[0]!
  | _ =>
    let n := xs.size
    xs[0:n-1].foldrM (init:=xs[n-1]!) fun x p => mkAppM ``Prod.mk #[x,p]

def toTerminationMeasures (preDefs : Array PreDefinition) (fixedParamPerms : FixedParamPerms)
    (userVarNamess : Array (Array Name)) (measuress : Array (Array BasicMeasure))
    (solution : Array MutualMeasure) : MetaM TerminationMeasures := do
  preDefs.mapIdxM fun funIdx preDef => do
    let measures := measuress[funIdx]!
    lambdaTelescope preDef.value fun params _ => do
      let xs := fixedParamPerms.perms[funIdx]!.pickVarying params
      withUserNames xs userVarNamess[funIdx]! do
        let args := solution.map fun
          | .args tmIdxs => measures[tmIdxs[funIdx]!]!.fn.beta params
          | .func funIdx' => mkNatLit <| if funIdx' == funIdx then 1 else 0
        let fn ← mkLambdaFVars params (← mkProdElem args)
        return { ref := .missing, structural := false, fn}

/--
Shows the inferred termination measure to the user, and implements `termination_by?`
-/
def reportTerminationMeasures (preDefs : Array PreDefinition) (termMeasures : TerminationMeasures) : MetaM Unit := do
  for preDef in preDefs, termMeasure in termMeasures do
    let stx := do
      let arity ← lambdaTelescope preDef.value fun xs _ => pure xs.size
      termMeasure.delab arity (extraParams := preDef.termination.extraParams)
    if showInferredTerminationBy.get (← getOptions) then
      logInfoAt preDef.ref m!"Inferred termination measure:\n{← stx}"
    if let some ref := preDef.termination.terminationBy?? then
      Tactic.TryThis.addSuggestion ref (← stx)

end GuessLex
open GuessLex

/--
Main entry point of this module:

Try to find a lexicographic ordering of the basic measures for which the recursive definition
terminates. See the module doc string for a high-level overview.

The `preDefs` are used to determine arity and types of parameters; the bodies are ignored.
-/
def guessLex (preDefs : Array PreDefinition) (unaryPreDef : PreDefinition)
    (fixedParamPerms : FixedParamPerms) (argsPacker : ArgsPacker) :
    MetaM TerminationMeasures := do
  let userVarNamess ← argsPacker.varNamess.mapM (naryVarNames ·)
  trace[Elab.definition.wf] "varNames is: {userVarNamess}"

  -- Collect all recursive calls and extract their context
  let recCalls ← collectRecCalls unaryPreDef fixedParamPerms argsPacker
  let recCalls := filterSubsumed recCalls

  -- For every function, the measures we want to use
  -- (One for each non-forbiddend arg)
  let basicMeassures₁ ← simpleMeasures preDefs fixedParamPerms userVarNamess
  let basicMeassures₂ ← complexMeasures preDefs fixedParamPerms userVarNamess recCalls
  let basicMeasures := Array.zipWith (· ++ ·) basicMeassures₁ basicMeassures₂

  -- The list of measures, including the measures that order functions.
  -- The function ordering measures come last
  let mutualMeasures ← generateMeasures (basicMeasures.map (·.size))

  -- If there is only one plausible measure, use that
  if let #[solution] := mutualMeasures then
    let termMeasures ← toTerminationMeasures preDefs fixedParamPerms userVarNamess basicMeasures #[solution]
    reportTerminationMeasures preDefs termMeasures
    return termMeasures

  let rcs ← recCalls.mapM (RecCallCache.mk (preDefs.map (·.declName)) (preDefs.map (·.termination.decreasingBy?)) basicMeasures ·)
  let callMatrix := rcs.map (inspectCall ·)

  match ← liftMetaM <| solve mutualMeasures callMatrix with
  | .some solution => do
    let termMeasures ← toTerminationMeasures preDefs fixedParamPerms userVarNamess basicMeasures solution
    reportTerminationMeasures preDefs termMeasures
    return termMeasures
  | .none =>
    let explanation ← explainFailure (preDefs.map (·.declName)) basicMeasures rcs
    Lean.throwError <| "Could not find a decreasing measure.\n" ++
      explanation ++ "\n" ++
      "Please use `termination_by` to specify a decreasing measure."
