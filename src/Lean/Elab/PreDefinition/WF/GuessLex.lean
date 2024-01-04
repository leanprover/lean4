/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
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
import Lean.Elab.PreDefinition.WF.PackMutual
import Lean.Data.Array


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

register_builtin_option showInferredTerminationBy : Bool := {
  defValue := false
  descr    := "In recursive definitions, show the inferred `termination_by` measure."
}

/--
Given a predefinition, find good variable names for its parameters.
Use user-given parameter names if present; use x1...xn otherwise.

The length of the returned array is also used to determine the arity
of the function, so it should match what `packDomain` does.

The names ought to accessible (no macro scopes) and still fresh wrt to the current environment,
so that with `showInferredTerminationBy` we can print them to the user reliably.
We do that by appending `'` as needed.
-/
partial
def naryVarNames (fixedPrefixSize : Nat) (preDef : PreDefinition) : MetaM (Array Name):= do
  lambdaTelescope preDef.value fun xs _ => do
    let xs := xs.extract fixedPrefixSize xs.size
    let mut ns : Array Name := #[]
    for h : i in [:xs.size] do
      let n ← (xs[i]'h.2).fvarId!.getUserName
      let n := if n.hasMacroScopes then .mkSimple s!"x{i+1}" else n
      ns := ns.push (← freshen ns n)
    return ns
  where
    freshen  (ns : Array Name) (n : Name): MetaM Name := do
      if !(ns.elem n) && (← resolveGlobalName n).isEmpty then
        return n
      else
        freshen ns (n.appendAfter "'")


/-- Internal monad used by `withRecApps` -/
abbrev M (recFnName : Name) (α β : Type) : Type :=
  StateRefT (Array α) (StateRefT (HasConstCache recFnName) MetaM) β

/--
Traverses the given expression `e`, and invokes the continuation `k`
at every saturated call to `recFnName`.

The expression `param` is passed along, and refined when going under a matcher
or `casesOn` application.
-/
partial def withRecApps {α} (recFnName : Name) (fixedPrefixSize : Nat) (param : Expr) (e : Expr)
    (k : Expr → Array Expr → MetaM α) : MetaM (Array α) := do
  trace[Elab.definition.wf] "withRecApps: {indentExpr e}"
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
    modifyGetThe (HasConstCache recFnName) (·.contains e)

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
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp param e
        else
          if let some altParams ← matcherApp.refineThrough? param then
            (Array.zip matcherApp.alts (Array.zip matcherApp.altNumParams altParams)).forM
              fun (alt, altNumParam, altParam) =>
                lambdaTelescope altParam fun xs altParam => do
                  -- TODO: Use boundedLambdaTelescope
                  unless altNumParam = xs.size do
                    throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
                  let altBody := alt.beta xs
                  loop altParam altBody
          else
            processApp param e
      | none =>
      match (← toCasesOnApp? e) with
      | some casesOnApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp param e
        else
          if let some altParams ← casesOnApp.refineThrough? param then
          (Array.zip casesOnApp.alts (Array.zip casesOnApp.altNumParams altParams)).forM
            fun (alt, altNumParam, altParam) =>
              lambdaTelescope altParam fun xs altParam => do
                -- TODO: Use boundedLambdaTelescope
                unless altNumParam = xs.size do
                  throwError "unexpected `casesOn` application alternative{indentExpr alt}\nat application{indentExpr e}"
                let altBody := alt.beta xs
                loop altParam altBody
          else
            processApp param e
      | none => processApp param e
    | e => do
      let _ ← ensureNoRecFn recFnName e

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
  /-- Syntax location of reursive call -/
  ref : Syntax
  /-- Function index of caller -/
  caller : Nat
  /-- Parameters of caller -/
  params : Array Expr
  /-- Function index of callee -/
  callee : Nat
  /-- Arguments to callee -/
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

/-- Traverse a unary PreDefinition, and returns a `WithRecCall` closure for each recursive
call site.
-/
def collectRecCalls (unaryPreDef : PreDefinition) (fixedPrefixSize : Nat) (arities : Array Nat)
    : MetaM (Array RecCallWithContext) := withoutModifyingState do
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
      RecCallWithContext.create (← getRef) caller params callee args

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

/-- Given an expression `e`, produce `sizeOf e` with a suitable instance. -/
def mkSizeOf (e : Expr) : MetaM Expr := do
  let ty ← inferType e
  let lvl ← getLevel ty
  let inst ← synthInstance (mkAppN (mkConst ``SizeOf [lvl]) #[ty])
  let res := mkAppN (mkConst ``sizeOf [lvl]) #[ty,  inst, e]
  check res
  return res

/--
For a given recursive call, and a choice of parameter and argument index,
try to prove equality, < or ≤.
-/
def evalRecCall (decrTactic? : Option Syntax) (rcc : RecCallWithContext) (paramIdx argIdx : Nat) :
    MetaM GuessLexRel := do
  rcc.ctxt.run do
    let param := rcc.params[paramIdx]!
    let arg := rcc.args[argIdx]!
    trace[Elab.definition.wf] "inspectRecCall: {rcc.caller} ({param}) → {rcc.callee} ({arg})"
    let arg ← mkSizeOf rcc.args[argIdx]!
    let param ← mkSizeOf rcc.params[paramIdx]!
    for rel in [GuessLexRel.eq, .lt, .le] do
      let goalExpr := mkAppN rel.toNatRel #[arg, param]
      trace[Elab.definition.wf] "Goal for {rel}: {goalExpr}"
      check goalExpr

      let mvar ← mkFreshExprSyntheticOpaqueMVar goalExpr
      let mvarId := mvar.mvarId!
      let mvarId ← mvarId.cleanup
      -- logInfo m!"Remaining goals: {goalsToMessageData [mvarId]}"
      try
        if rel = .eq then
          MVarId.refl mvarId
        else do
          Lean.Elab.Term.TermElabM.run' do
            match decrTactic? with
            | none =>
              let remainingGoals ← Tactic.run mvarId do
                Tactic.evalTactic (← `(tactic| decreasing_tactic))
              remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]
              -- trace[Elab.definition.wf] "Found {rel} proof: {← instantiateMVars mvar}"
              pure ()
            | some decrTactic => Term.withoutErrToSorry do
              -- make info from `runTactic` available
              pushInfoTree (.hole mvarId)
              Term.runTactic mvarId decrTactic
              -- trace[Elab.definition.wf] "Found {rel} proof: {← instantiateMVars mvar}"
              pure ()
        trace[Elab.definition.wf] "inspectRecCall: success!"
        return rel
      catch _e =>
        trace[Elab.definition.wf] "Did not find {rel} proof: {goalsToMessageData [mvarId]}"
        continue
    return .no_idea

/- A cache for `evalRecCall` -/
structure RecCallCache where mk'' ::
  decrTactic? : Option Syntax
  rcc : RecCallWithContext
  cache : IO.Ref (Array (Array (Option GuessLexRel)))

/-- Create a cache to memoize calls to `evalRecCall descTactic? rcc` -/
def RecCallCache.mk (decrTactic? : Option Syntax) (rcc : RecCallWithContext) :
    BaseIO RecCallCache := do
  let cache ← IO.mkRef <| Array.mkArray rcc.params.size (Array.mkArray rcc.args.size Option.none)
  return { decrTactic?, rcc, cache }

/-- Run `evalRecCall` and cache there result -/
def RecCallCache.eval (rc: RecCallCache) (paramIdx argIdx : Nat) : MetaM GuessLexRel := do
  -- Check the cache first
  if let Option.some res := (← rc.cache.get)[paramIdx]![argIdx]! then
    return res
  else
    let res ← evalRecCall rc.decrTactic? rc.rcc paramIdx argIdx
    rc.cache.modify (·.modify paramIdx (·.set! argIdx res))
    return res


/-- Print a single cache entry as a string, without forcing it -/
def RecCallCache.prettyEntry (rcc : RecCallCache) (paramIdx argIdx : Nat) : MetaM String := do
  let cachedEntries ← rcc.cache.get
  return match cachedEntries[paramIdx]![argIdx]! with
  | .some rel => toString rel
  | .none => "_"

/-- The measures that we order lexicographically can be comparing arguments,
or numbering the functions -/
inductive MutualMeasure where
  /-- For every function, the given argument index -/
  | args : Array Nat → MutualMeasure
  /-- The given function index is assigned 1, the rest 0 -/
  | func : Nat → MutualMeasure

/-- Evaluate a recursive call at a given `MutualMeasure` -/
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
These arguments should not be considered when guessing a well-founded relation.
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


/--
Generate all combination of arguments, skipping those that are forbidden.

Sorts the uniform combinations ([0,0,0], [1,1,1]) to the front; they are commonly most useful to
try first, when the mutually recursive functions have similar argument structures
-/
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


/--
Enumerate all meausures we want to try: All arguments (resp. combinations thereof) and
possible orderings of functions (if more than one)
-/
def generateMeasures (forbiddenArgs : Array (Array Nat)) (arities : Array Nat) :
    MetaM (Array MutualMeasure) := do
  let some arg_measures := generateCombinations? forbiddenArgs arities
      | throwError "Too many combinations"

  let func_measures :=
    if arities.size > 1 then
      (List.range arities.size).toArray
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

/--
Create Tuple syntax (`()` if the array is empty, and just the value if its a singleton)
-/
def mkTupleSyntax : Array Term → MetaM Term
  | #[]  => `(())
  | #[e] => return e
  | es   => `(($(es[0]!), $(es[1:]),*))

/--
Given an array of `MutualMeasures`, creates a `TerminationWF` that specifies the lexicographic
combination of these measures.
-/
def buildTermWF (declNames : Array Name) (varNamess : Array (Array Name))
    (measures : Array MutualMeasure) : MetaM TerminationWF := do
  let mut termByElements := #[]
  for h : funIdx in [:varNamess.size] do
    let vars := (varNamess[funIdx]'h.2).map mkIdent
    let body ← mkTupleSyntax (← measures.mapM fun
      | .args varIdxs => do
          let v := vars.get! (varIdxs[funIdx]!)
          let sizeOfIdent := mkIdent (← unresolveNameGlobal ``sizeOf)
          `($sizeOfIdent $v)
      | .func funIdx' => if funIdx' == funIdx then `(1) else `(0)
      )
    let declName := declNames[funIdx]!

    termByElements := termByElements.push
      { ref := .missing
        declName, vars, body,
        implicit := true
      }
  return termByElements


/--
Given a matrix (row-major) of strings, arranges them in tabular form.
First column is left-aligned, others right-aligned.
Single space as column separator.
-/
def formatTable : Array (Array String) → String := fun xss => Id.run do
  let mut colWidths := xss[0]!.map (fun _ => 0)
  for i in [:xss.size] do
    for j in [:xss[i]!.size] do
      if xss[i]![j]!.length > colWidths[j]! then
        colWidths := colWidths.set! j xss[i]![j]!.length
  let mut str := ""
  for i in [:xss.size] do
    for j in [:xss[i]!.size] do
      let s := xss[i]![j]!
      if j > 0 then -- right-align
        for _ in [:colWidths[j]! - s.length] do
          str := str ++ " "
      str := str ++ s
      if j = 0 then -- left-align
        for _ in [:colWidths[j]! - s.length] do
          str := str ++ " "
      if j + 1 < xss[i]!.size then
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


/-- Explain what we found out about the recursive calls (non-mutual case) -/
def explainNonMutualFailure (varNames : Array Name) (rcs : Array RecCallCache) : MetaM Format := do
  let header := varNames.map (·.eraseMacroScopes.toString)
  let mut table : Array (Array String) := #[#[""] ++ header]
  for i in [:rcs.size], rc in rcs do
    let mut row := #[s!"{i+1}) {← rc.rcc.posString}"]
    for argIdx in [:varNames.size] do
      row := row.push (← rc.prettyEntry argIdx argIdx)
    table := table.push row

  return formatTable table

/-- Explain what we found out about the recursive calls (mutual case) -/
def explainMutualFailure (declNames : Array Name) (varNamess : Array (Array Name))
    (rcs : Array RecCallCache) : MetaM Format := do
  let mut r := Format.nil

  for rc in rcs do
    let caller := rc.rcc.caller
    let callee := rc.rcc.callee
    r := r ++ f!"Call from {declNames[caller]!} to {declNames[callee]!} " ++
      f!"at {← rc.rcc.posString}:\n"

    let header := varNamess[caller]!.map (·.eraseMacroScopes.toString)
    let mut table : Array (Array String) := #[#[""] ++ header]
    if caller = callee then
      -- For self-calls, only the diagonal is interesting, so put it into one row
      let mut row := #[""]
      for argIdx in [:varNamess[caller]!.size] do
        row := row.push (← rc.prettyEntry argIdx argIdx)
      table := table.push row
    else
      for argIdx in [:varNamess[callee]!.size] do
        let mut row := #[]
        row := row.push varNamess[callee]![argIdx]!.eraseMacroScopes.toString
        for paramIdx in [:varNamess[caller]!.size] do
          row := row.push (← rc.prettyEntry paramIdx argIdx)
        table := table.push row
    r := r ++ formatTable table ++ "\n"

  return r

def explainFailure (declNames : Array Name) (varNamess : Array (Array Name))
    (rcs : Array RecCallCache) : MetaM Format := do
  let mut r : Format := "The arguments relate at each recursive call as follows:\n" ++
    "(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)\n"
  if declNames.size = 1 then
    r := r ++ (← explainNonMutualFailure varNamess[0]! rcs)
  else
    r := r ++ (← explainMutualFailure declNames varNamess rcs)
  return r

end Lean.Elab.WF.GuessLex

namespace Lean.Elab.WF

open Lean.Elab.WF.GuessLex

/--
Main entry point of this module:

Try to find a lexicographic ordering of the arguments for which the recursive definition
terminates. See the module doc string for a high-level overview.
-/
def guessLex (preDefs : Array PreDefinition)  (unaryPreDef : PreDefinition)
    (fixedPrefixSize : Nat) (decrTactic? : Option Syntax) :
    MetaM TerminationWF := do
  let varNamess ← preDefs.mapM (naryVarNames fixedPrefixSize ·)
  let arities := varNamess.map (·.size)
  trace[Elab.definition.wf] "varNames is: {varNamess}"

  let forbiddenArgs ← preDefs.mapM fun preDef =>
    getForbiddenByTrivialSizeOf fixedPrefixSize preDef

  -- The list of measures, including the measures that order functions.
  -- The function ordering measures come last
  let measures ← generateMeasures forbiddenArgs arities

  -- If there is only one plausible measure, use that
  if let #[solution] := measures then
    return ← buildTermWF (preDefs.map (·.declName)) varNamess #[solution]

  -- Collect all recursive calls and extract their context
  let recCalls ← collectRecCalls unaryPreDef fixedPrefixSize arities
  let recCalls := filterSubsumed recCalls
  let rcs ← recCalls.mapM (RecCallCache.mk decrTactic? ·)
  let callMatrix := rcs.map (inspectCall ·)

  match ← liftMetaM <| solve measures callMatrix with
  | .some solution => do
    let wf ← buildTermWF (preDefs.map (·.declName)) varNamess solution

    let wfStx ← withoutModifyingState do
      preDefs.forM (addAsAxiom ·)
      wf.unexpand

    if showInferredTerminationBy.get (← getOptions) then
      logInfo m!"Inferred termination argument:{wfStx}"

    return wf
  | .none =>
    let explanation ← explainFailure (preDefs.map (·.declName)) varNamess rcs
    Lean.throwError <| "Could not find a decreasing measure.\n" ++
      explanation ++ "\n" ++
      "Please use `termination_by` to specify a decreasing measure."
