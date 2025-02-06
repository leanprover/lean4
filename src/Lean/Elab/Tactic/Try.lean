/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Try
import Init.Grind.Tactics
import Lean.Meta.Tactic.ExposeNames
import Lean.Meta.Tactic.Try
import Lean.Meta.Tactic.TryThis
import Lean.Elab.Tactic.Config
import Lean.Elab.Tactic.SimpTrace
import Lean.Elab.Tactic.Grind

namespace Lean.Elab.Tactic
open Meta
/-!
A **very** simple `try?` tactic implementation.
-/

declare_config_elab elabTryConfig Try.Config

namespace Try

/-!
`evalSuggest` is a `evalTactic` variant that returns suggestions after executing a tactic built using
combinatiors such as `first`, `attempt_all`, `<;>`, `;`, and `try`.
-/

/-- Returns the suggestions represented by `tac`.  -/
private def getSuggestionOfTactic (tac : TSyntax `tactic) : Array (TSyntax `tactic) :=
  match tac with
  | `(tactic| try_suggestions $tacs*) => tacs
  | _ => #[tac]

/-- Adds `tac` to `suggestions`. -/
private def appendSuggestion (suggestions : Array (TSyntax `tactic)) (tac : TSyntax `tactic) : Array (TSyntax `tactic) :=
  suggestions ++ getSuggestionOfTactic tac

/-- Returns a tactic representing all given suggestions `tacs`. -/
private def mkTrySuggestions (tacs : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  if tacs.isEmpty then
    throwError "`mkTrySuggestions` failed"
  else if tacs.size == 1 then
    return tacs[0]!
  else
    `(tactic| try_suggestions $tacs*)

/-- Erases tactics `skip` and `done` from `tacs` -/
private def filterSkipDone (tacs : Array (TSyntax `tactic)) : Array (TSyntax `tactic) :=
  tacs.filter fun tac => match tac with
    | `(tactic| done) | `(tactic| skip) => false
    | _ => true

private def mkSeq (tacs : Array (TSyntax `tactic)) (terminal : Bool) : CoreM (TSyntax `tactic) := do
  let tacs := filterSkipDone tacs
  if tacs.size = 0 then
    if terminal then `(tactic| done) else `(tactic| skip)
  else if tacs.size = 1 then
    return tacs[0]!
  else if terminal then
    `(tactic| · $tacs;*)
  else
    `(tactic| ($tacs;*))

/-- Returns `true` if `tac` is `sorry` -/
private def isSorry (tac : TSyntax `tactic) : Bool :=
  match tac with
  | `(tactic| sorry) => true
  | _ => false

/-- Erases `sorry` tactics from `s` -/
private def filterSorry (s : Array (TSyntax `tactic)) : Array (TSyntax `tactic) :=
  s.filter fun stx => match stx with
    | `(tactic| sorry) => false
    | _ => true

/-- Erases duplicate tactics from `s`. -/
private def removeDuplicates (s : Array (TSyntax `tactic)) : Array (TSyntax `tactic) := Id.run do
  let mut r := #[]
  for t in s do
    unless r.contains t do
      r := r.push t
  return r

private def getSuggestionsCore (tac : TSyntax `tactic): Array (TSyntax `tactic) :=
  let tacs := getSuggestionOfTactic tac
  let tacs := filterSorry tacs
  removeDuplicates tacs

/-- Return tactics that could solve all subgoals. -/
private def getTacsSolvedAll (tacs2 : Array (Array (TSyntax `tactic))) : Array (TSyntax `tactic) := Id.run do
  if tacs2.isEmpty then
    return #[]
  else
    let mut r := #[]
    for tac2 in tacs2[0]! do
      if tacs2[1:].all (·.contains tac2) then
        r := r.push tac2
    return r

/-- Erases from `tacss` tactics occurring in `tacs`. -/
private def eraseTacs (tacss : Array (Array (TSyntax `tactic))) (tacs : Array (TSyntax `tactic)) : Array (Array (TSyntax `tactic)) :=
  tacss.map fun ts => ts.filter fun t => !tacs.contains t

/-- Returns tactic kinds that could solve all subgoals. -/
private def getKindsSolvedAll (tacss : Array (Array (TSyntax `tactic))) : Array SyntaxNodeKind := Id.run do
  if tacss.isEmpty then
    return #[]
  else
    let mut r := #[]
    for tacs0 in tacss[0]! do
      let k := tacs0.raw.getKind
      if tacss[1:].all fun tacs => tacs.any fun tac => tac.raw.getKind == k then
        r := r.push k
    return r

private def peekOne (tac1 : TSyntax `tactic) (tacss2 : Array (Array (TSyntax `tactic))) : TacticM (TSyntax `tactic) := do
  let mut tacs2 := #[]
  for s in tacss2 do
    if s.isEmpty then
      tacs2 := tacs2.push (← `(tactic| · sorry))
    else
      tacs2 := tacs2.push (← `(tactic| · $(s[0]!):tactic))
  `(tactic| · $tac1:tactic
              $tacs2*)

private def mkChainResult (tac1 : TSyntax `tactic) (tacss2 : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  let tacss2 := tacss2.map getSuggestionsCore
  if (← isTracingEnabledFor `try.debug) then
    trace[try.debug] "mkChainResultCore tac1{indentD tac1}"
    let mut i : Nat := 0
    for tacs2 in tacss2 do
      i := i + 1
      trace[try.debug] "goal #{i} tactics"
      for tac2 in tacs2 do
        trace[try.debug] "  {tac2}"
    trace[try.debug] "mkChainResult -----"
  let mut acc := #[]
  let solvedAll := getTacsSolvedAll tacss2
  for tac2 in solvedAll do
    acc := acc.push (← `(tactic| $tac1 <;> $tac2))
  let tacss2 := eraseTacs tacss2 solvedAll
  -- TODO: mixed cases
  trace[try.debug] "kinds: {getKindsSolvedAll tacss2}"
  if (!acc.isEmpty && tacss2.all fun s => !s.isEmpty)
     -- We only include partial solutions if there are no other solutions.
     || (acc.isEmpty && tacss2.any fun s => !s.isEmpty) then
    acc := acc.push <| (← peekOne tac1 tacss2)
  mkTrySuggestions acc

private def evalSuggestAtomic (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  let goals ← getGoals
  evalTactic tac.raw
  let goals' ← getGoals
  if goals == goals' then
    `(tactic| skip)
  else
    return tac

private def grindTraceToGrind (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  match tac with
  | `(tactic| grind? $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    `(tactic| grind $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?)
  | _ => throwUnsupportedSyntax

private def simpTraceToSimp (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  match tac with
  | `(tactic| simp? $config:optConfig $[only%$only]? $[[$args,*]]? $(loc)?) =>
    `(tactic| simp $config:optConfig $[only%$only]? $[[$args,*]]? $(loc)?)
  | _ => throwUnsupportedSyntax

private def evalSuggestGrindTrace (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
  match tac with
  | `(tactic| grind? $configStx:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    let config ← elabGrindConfig configStx
    let config := { config with trace := true, verbose := false }
    let trace ← evalGrindCore tac config only params fallback?
    let tac ← grindTraceToGrind tac
    let tac' ← mkGrindOnly configStx fallback? trace
    trace[try.debug] "`grind` succeeded"
    mkTrySuggestions #[tac, tac']
  | _ => throwUnsupportedSyntax

private def evalSuggestSimpTrace (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := withMainContext do
  match tac with
  | `(tactic| simp? $_:optConfig $[only%$only]? $[[$args,*]]? $(loc)?) =>
    let tac ← simpTraceToSimp tac
    let { ctx, simprocs, .. } ← mkSimpContext tac (eraseLocal := false)
    let stats ← simpLocation ctx (simprocs := simprocs) none <| (loc.map expandLocation).getD (.targets #[] true)
    let tac' ← mkSimpCallStx tac stats.usedTheorems
    trace[try.debug] "`simp` succeeded"
    mkTrySuggestions #[tac, tac']
  | _ => throwUnsupportedSyntax

abbrev TacticResult (α : Type) := EStateM.Result Exception SavedState α

structure Ctx where
  root : TSyntax `tactic
  terminal : Bool
  config : Try.Config

abbrev M := ReaderT Ctx TacticM

instance : MonadBacktrack SavedState M where
  saveState := fun _ => saveState
  restoreState s := fun _ => restoreState s

abbrev withNonTerminal (x : M α) : M α :=
  withReader (fun c => { c with terminal := false}) x

-- TODO: polymorphic `Tactic.focus`
abbrev focus (x : M α) : M α := fun ctx => Tactic.focus (x ctx)

def observing (x : M α) : M (TacticResult α) := do
  let s ← saveState
  try
    let e ← x
    let sNew ← saveState
    s.restore (restoreInfo := true)
    return EStateM.Result.ok e sNew
  catch
    | ex =>
      let sNew ← saveState
      s.restore (restoreInfo := true)
      return .error ex sNew

@[extern "lean_eval_suggest_tactic"] -- forward definition to avoid mutual block
opaque evalSuggest (tac : TSyntax `tactic) : M (TSyntax `tactic)

/-- `evalSuggest` for `tac1 <;> tac2` -/
private def evalSuggestChain (tac1 tac2 : TSyntax `tactic) : M (TSyntax `tactic) := focus do
  unless (← read).terminal do
    throwError "invalid `<;>` occurrence in non-terminal position for `try?` script{indentD (← read).root}"
  let tac1 ← withNonTerminal do evalSuggest tac1
  let goals ← getGoals
  setGoals []
  let mut tac2s := #[]
  let mut i : Nat := 0
  for goal in goals do
    setGoals [goal]
    let tac2' : TSyntax `tactic ← (evalSuggest tac2) <|> `(tactic| sorry)
    i := i + 1
    tac2s := tac2s.push tac2'
  if tac2s.all isSorry then
    throwError "`<;>` failed"
  mkChainResult tac1 tac2s

/-- `evalSuggest` for a sequence of tactics. -/
private def evalSuggestSeq (tacs : Array (TSyntax `tactic)) : M (TSyntax `tactic) := do
  if (← read).terminal then
    let mut result := #[]
    for i in [:tacs.size - 1] do
      result := result.push (← withNonTerminal <| evalSuggest tacs[i]!)
    let suggestions ← getSuggestionOfTactic (← evalSuggest tacs.back!) |>.mapM fun tac =>
      mkSeq (result.push tac) (terminal := true)
    mkTrySuggestions suggestions
  else
    mkSeq (← tacs.mapM evalSuggest) (terminal := false)

private def evalSuggestSeqCore (tacs : Array Syntax) : M (TSyntax `tactic) := do
  evalSuggestSeq (tacs.map fun tac => ⟨tac⟩)

private def evalSuggestTacticSeq (s : TSyntax ``Parser.Tactic.tacticSeq) : M (TSyntax `tactic) := do
  let tacs ← match s with
    | `(tacticSeq| { $t;* }) => pure t.getElems
    | `(tacticSeq| $t;*) => pure t.getElems
    | _ => throwError "unexpeted sequence"
  evalSuggestSeq tacs

/-- `evalSuggest` for `first` tactic. -/
private partial def evalSuggestFirst (tacs : Array (TSyntax ``Parser.Tactic.tacticSeq)) : M (TSyntax `tactic) := do
  go 0
where
  go (i : Nat) : M (TSyntax `tactic) := do
    if i = tacs.size - 1 then
      evalSuggestTacticSeq tacs[i]!
    else
      evalSuggestTacticSeq tacs[i]! <|> go (i+1)

/-- `evalSuggest` for `try` tactic. -/
private partial def evalSuggestTry (tac : TSyntax ``Parser.Tactic.tacticSeq) : M (TSyntax `tactic) := do
  (do evalSuggestTacticSeq tac)
  <|>
  `(tactic| skip)

/-- `evalSuggest` for `attempt_all` tactic. -/
private partial def evalSuggestAttemptAll (tacs : Array (TSyntax ``Parser.Tactic.tacticSeq)) : M (TSyntax `tactic) := do
  unless (← read).terminal do
    throwError "invalid occurrence of `attempt_all` in non-terminal position for `try?` script{indentD (← read).root}"
  go 0 none #[]
where
  go (i : Nat) (saved? : Option SavedState) (acc : Array (TSyntax `tactic)) : M (TSyntax `tactic) := do
    if i < tacs.size then
      match (← observing (evalSuggestTacticSeq tacs[i]!)) with
      | .ok tac s =>
        trace[try.debug] "`attempt_all` argument succeeded{indentD tac}"
        go (i+1) (saved? <|> some s) (appendSuggestion acc tac)
      | _ =>
        go (i+1) saved? acc
    else
      if let some saved := saved? then
        saved.restore
        mkTrySuggestions acc
      else
        throwError "`attempt_all` failed"

-- `evalSuggest` implementation
@[export lean_eval_suggest_tactic]
private partial def evalSuggestImpl (tac : TSyntax `tactic) : M (TSyntax `tactic) := do
  match tac with
  | `(tactic| $tac1 <;> $tac2) => evalSuggestChain tac1 tac2
  | `(tactic| first $[| $tacs]*) => evalSuggestFirst tacs
  | `(tactic| ($tac:tacticSeq)) => evalSuggestTacticSeq tac
  | `(tactic| try $tac:tacticSeq) => evalSuggestTry tac
  | `(tactic| attempt_all $[| $tacs]*) => evalSuggestAttemptAll tacs
  | _ =>
    let k := tac.raw.getKind
    if k == ``Parser.Tactic.seq1 then
      evalSuggestSeqCore tac.raw[0].getSepArgs
    else
      let r ← if k == ``Parser.Tactic.grindTrace then
        evalSuggestGrindTrace tac
      else if k == ``Parser.Tactic.simpTrace then
        evalSuggestSimpTrace tac
      else
        evalSuggestAtomic tac
      if (← read).terminal then
        unless (← getGoals).isEmpty do
          throwError "unsolved goals"
      return r

private def toSuggestion (t : TSyntax `tactic) : Tactic.TryThis.Suggestion :=
  t

private def getSuggestions (tac : TSyntax `tactic) : Array Tactic.TryThis.Suggestion :=
  let tacs := getSuggestionsCore tac
  tacs.map toSuggestion

private def throwEvalAndSuggestFailed : TacticM Unit := do
  let goal ← getMainGoal
  Meta.throwTacticEx `«try?» goal "consider using `grind` manually"

private def addSuggestions (tk : Syntax) (s : Array Tactic.TryThis.Suggestion) : TacticM Unit := do
  if s.size == 1 then
    Tactic.TryThis.addSuggestion tk s[0]! (origSpan? := (← getRef))
  else
    Tactic.TryThis.addSuggestions tk (s.map fun stx => stx) (origSpan? := (← getRef))

def evalAndSuggest (tk : Syntax) (tac : TSyntax `tactic) (config : Try.Config := {}) : TacticM Unit := do
  let tac' ← evalSuggest tac |>.run { terminal := true, root := tac, config }
  let s := getSuggestions tac'
  if s.isEmpty then
    throwEvalAndSuggestFailed
  else
    addSuggestions tk s

/-! Helper functions -/

/-- Converts a declaraion name into an identifier. -/
private def toIdent (declName : Name) : MetaM Ident := do
  return mkIdent (← unresolveNameGlobalAvoidingLocals declName)

private def mkFirstStx (tacs : Array (TSyntax `tactic)) : CoreM (TSyntax `tactic) :=
  if tacs.size = 1 then
    return tacs[0]!
  else
    `(tactic| first $[| $tacs:tactic]*)

/-! `grind` tactic syntax generator based on collected information. -/

/-- Given a `grind` tactic syntax `tac`, sets its parameters using `params`. -/
private def setGrindParams (tac : TSyntax `tactic) (params : Array (TSyntax ``Parser.Tactic.grindParam)) : TSyntax `tactic :=
  let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
  ⟨tac.raw.setArg 3 (mkNullNode paramsStx)⟩

/-- Given a set of declaration names, returns `grind` parameters of the form `= <declName>` -/
private def mkGrindEqnParams (declNames : Array Name) : MetaM (Array (TSyntax ``Parser.Tactic.grindParam)) := do
  declNames.mapM fun declName => do
    `(Parser.Tactic.grindParam| = $(← toIdent declName))

private def mkGrindStx (info : Try.Info) : MetaM (TSyntax `tactic) := do
  let grind ← `(tactic| grind?)
  let mut tacs := #[grind]
  unless info.eqnCandidates.isEmpty do
    tacs := tacs.push (setGrindParams grind (← mkGrindEqnParams info.eqnCandidates.elems))
  unless info.unfoldCandidates.isEmpty do
    tacs := tacs.push (setGrindParams grind (← mkGrindEqnParams info.unfoldCandidates.elems))
  mkFirstStx tacs

/-! Other generators -/

set_option hygiene false in -- Avoid tagger at `+arith`
/-- `simp` tactic syntax generator -/
private def mkSimpStx : CoreM (TSyntax `tactic) :=
  `(tactic| first | simp?; done | simp? +arith; done | simp_all; done)

/-- `simple` tactics -/
private def mkSimpleTacStx : CoreM (TSyntax `tactic) :=
  `(tactic| attempt_all | rfl | assumption | contradiction)

/-! Function induction generators -/

private def allAccessible (majors : Array FVarId) : MetaM Bool :=
  majors.allM fun major => do
    let localDecl ← major.getDecl
    if localDecl.userName.hasMacroScopes then
      return false
    else
      -- Check whether variable has been shadowed
      let some localDecl' := (← getLCtx).findFromUserName? localDecl.userName
        | return false
      return localDecl'.fvarId == localDecl.fvarId

open Try.Collector in
private def mkFunIndStx (c : FunIndCandidate) (cont : TSyntax `tactic) : MetaM (TSyntax `tactic) := do
  if (← allAccessible c.majors) then
    go
  else withNewMCtxDepth do
    -- Create a helper goal to apply
    let mvarId := (← mkFreshExprMVar (mkConst ``True)).mvarId!
    let mvarId ← mvarId.exposeNames
    mvarId.withContext do
      `(tactic| (expose_names; $(← go):tactic))
where
  go : MetaM (TSyntax `tactic) := do
    let mut terms := #[]
    for major in c.majors do
      let localDecl ← major.getDecl
      terms := terms.push (← `($(mkIdent localDecl.userName):term))
    let indFn ← toIdent c.funIndDeclName
    `(tactic| induction $terms,* using $indFn <;> $cont)

private def mkAllFunIndStx (info : Try.Info) (cont : TSyntax `tactic) : MetaM (TSyntax `tactic) := do
  let tacs ← info.funIndCandidates.elems.mapM (mkFunIndStx · cont)
  mkFirstStx tacs

/-! Main code -/

/-- Returns tactic for `evalAndSuggest` -/
private def mkTryEvalSuggestStx (info : Try.Info) : MetaM (TSyntax `tactic) := do
  let simple ← mkSimpleTacStx
  let simp ← mkSimpStx
  let grind ← mkGrindStx info
  let atomic ← `(tactic| attempt_all | $simple:tactic | $simp:tactic | $grind:tactic)
  let funInds ← mkAllFunIndStx info atomic
  `(tactic| first | $atomic:tactic | $funInds:tactic)

-- TODO: vanilla `induction`.
-- TODO: make it extensible.
-- TODO: librarySearch integration.
-- TODO: premise selection.

@[builtin_tactic Lean.Parser.Tactic.tryTrace] def evalTryTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| try?%$tk $config:optConfig) => Tactic.focus do withMainContext do
    let config ← elabTryConfig config
    let info ← Try.collect (← getMainGoal) config
    let stx ← mkTryEvalSuggestStx info
    evalAndSuggest tk stx config
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Try
