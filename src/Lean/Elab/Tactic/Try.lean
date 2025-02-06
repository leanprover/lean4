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

namespace Lean.Parser.Tactic
/-- Internal tactic used to implement `evalSuggest` -/
syntax (name := tryResult) "try_suggestions " tactic* : tactic
end Lean.Parser.Tactic

namespace Lean.Elab.Tactic
open Meta
/-!
A **very** simple `try?` tactic implementation.
-/

declare_config_elab elabTryConfig Try.Config

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

/--
Given the suggestion sequecences `suggestionsSeqs`, extends each sequence using `tac`.
-/
private def appendSeqResult (suggestionSeqs : Array (Array (TSyntax `tactic))) (tac : TSyntax `tactic) : Array (Array (TSyntax `tactic)) :=
  match tac with
  | `(tactic| try_suggestions $tacs:tactic*) => suggestionSeqs.foldl (init := #[]) fun result seq => result ++ tacs.map (seq.push ·)
  | _ => suggestionSeqs.map (·.push tac)

/-- Returns a tactic representing all given suggestions `tacs`. -/
private def mkTrySuggestions (tacs : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  if tacs.isEmpty then
    throwError "`mkSuggestions` failed"
  else if tacs.size == 1 then
    return tacs[0]!
  else
    `(tactic| try_suggestions $tacs*)

/-- Erases tactics `skip` and `done` from `tacs` -/
private def filterSkipDone (tacs : Array (TSyntax `tactic)) : Array (TSyntax `tactic) :=
  tacs.filter fun tac => match tac with
    | `(tactic| done) | `(tactic| skip) => false
    | _ => true

/--
Returns a tactic representing the given suggestions.
-/
private def mkSeqResult (suggestionSeqs : Array (Array (TSyntax `tactic))) : TacticM (TSyntax `tactic) := do
  let tacs ← suggestionSeqs.mapM fun tacs => do
    let tacs := filterSkipDone tacs
    if tacs.size = 0 then
      `(tactic| done)
    else if tacs.size = 1 then
      return tacs[0]!
    else
      `(tactic| · $tacs;*)
  mkTrySuggestions tacs

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

private def mkChainResultCore (tac1 : TSyntax `tactic) (tacs2 : Array (TSyntax `tactic)) : TacticM (Array (TSyntax `tactic)) := do
  let tacs2 := tacs2.map getSuggestionsCore
  let mut acc := #[]
  let solvedAll := getTacsSolvedAll tacs2
  for tac2 in solvedAll do
    acc := acc.push (← `(tactic| $tac1 <;> $tac2))
  let tacs2 := eraseTacs tacs2 solvedAll
  -- TODO: mixed cases
  trace[Meta.debug] "CHAIN tacs2: {tacs2}"
  trace[Meta.debug] "CHAIN kinds: {getKindsSolvedAll tacs2}"
  return acc

private def mkChainResult (tac1 : TSyntax `tactic) (tacs2 : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  match tac1 with
  | `(tactic| try_suggestions $tacs1:tactic*) =>
    let tacs ← tacs1.foldlM (init := #[]) fun acc tac1 => return acc ++ (← mkChainResultCore tac1 tacs2)
    mkTrySuggestions tacs
  | _ => mkTrySuggestions (← mkChainResultCore tac1 tacs2)

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
    mkTrySuggestions #[tac, tac']
  | _ => throwUnsupportedSyntax

private def evalSuggestSimpTrace (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := withMainContext do
  match tac with
  | `(tactic| simp? $_:optConfig $[only%$only]? $[[$args,*]]? $(loc)?) =>
    let tac ← simpTraceToSimp tac
    let { ctx, simprocs, .. } ← mkSimpContext tac (eraseLocal := false)
    let stats ← simpLocation ctx (simprocs := simprocs) none <| (loc.map expandLocation).getD (.targets #[] true)
    let tac' ← mkSimpCallStx tac stats.usedTheorems
    mkTrySuggestions #[tac, tac']
  | _ => throwUnsupportedSyntax

abbrev TacticResult (α : Type) := EStateM.Result Exception SavedState α

def observing (x : TacticM α) : TacticM (TacticResult α) := do
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
opaque evalSuggest (tac : TSyntax `tactic) : TacticM (TSyntax `tactic)

/-- `evalSuggest` for `tac1 <;> tac2` -/
private def evalSuggestChain (tac1 tac2 : TSyntax `tactic) : TacticM (TSyntax `tactic) := focus do
  let tac1 ← evalSuggest tac1
  let goals ← getGoals
  setGoals []
  let mut tac2s := #[]
  for goal in goals do
    setGoals [goal]
    let tac2' ← (evalSuggest tac2) <|> `(tactic| sorry)
    unless (← getGoals).isEmpty do
      throwError "unsolved goals, `<;>` in `try?` requires all goals to be solved"
    tac2s := tac2s.push tac2'
  if tac2s.all isSorry then
    throwError "`<;>` failed"
  mkChainResult tac1 tac2s

/-- `evalSuggest` for a sequence of tactics. -/
private def evalSuggestSeq (tacs : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
  go 0 #[#[]]
where
  go (i : Nat) (accs : Array (Array (TSyntax `tactic))) : TacticM (TSyntax `tactic) := do
    if i < tacs.size then
      let tac' ← evalSuggest tacs[i]!
      go (i+1) (appendSeqResult accs tac')
    else
      mkSeqResult accs

private def evalSuggestSeqCore (tacs : Array Syntax) : TacticM (TSyntax `tactic) := do
  evalSuggestSeq (tacs.map fun tac => ⟨tac⟩)

private def evalSuggestTacticSeq (s : TSyntax ``Parser.Tactic.tacticSeq) : TacticM (TSyntax `tactic) := do
  let tacs ← match s with
    | `(tacticSeq| { $t;* }) => pure t.getElems
    | `(tacticSeq| $t;*) => pure t.getElems
    | _ => throwError "unexpeted sequence"
  evalSuggestSeq tacs

/-- `evalSuggest` for `first` tactic. -/
private partial def evalSuggestFirst (tacs : Array (TSyntax ``Parser.Tactic.tacticSeq)) : TacticM (TSyntax `tactic) := do
  go 0
where
  go (i : Nat) : TacticM (TSyntax `tactic) := do
    if i = tacs.size - 1 then
      evalSuggestTacticSeq tacs[i]!
    else
      evalSuggestTacticSeq tacs[i]! <|> go (i+1)

/-- `evalSuggest` for `try` tactic. -/
private partial def evalSuggestTry (tac : TSyntax ``Parser.Tactic.tacticSeq) : TacticM (TSyntax `tactic) := do
  (do evalSuggestTacticSeq tac)
  <|>
  `(tactic| skip)

/-- `evalSuggest` for `attempt_all` tactic. -/
private partial def evalSuggestAttemptAll (tacs : Array (TSyntax ``Parser.Tactic.tacticSeq)) : TacticM (TSyntax `tactic) := do
  go 0 none #[]
where
  go (i : Nat) (saved? : Option SavedState) (acc : Array (TSyntax `tactic)) : TacticM (TSyntax `tactic) := do
    if i < tacs.size then
      match (← observing (evalSuggestTacticSeq tacs[i]!)) with
      | .ok tac s => go (i+1) (saved? <|> some s) (appendSuggestion acc tac)
      | _ => go (i+1) saved? acc
    else
      if let some saved := saved? then
        saved.restore
        mkTrySuggestions acc
      else
        throwError "`attempt_all` failed"

-- `evalSuggest` implementation
@[export lean_eval_suggest_tactic]
private partial def evalSuggestImpl (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := do
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
    else if k == ``Parser.Tactic.grindTrace then
      evalSuggestGrindTrace tac
    else if k == ``Parser.Tactic.simpTrace then
      evalSuggestSimpTrace tac
    else
      evalSuggestAtomic tac

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

def evalAndSuggest (tk : Syntax) (tac : TSyntax `tactic) : TacticM Unit := do
  let tac' ← evalSuggest tac
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
private def mkGrindEqnParams (declNames : Std.HashSet Name) : MetaM (Array (TSyntax ``Parser.Tactic.grindParam)) := do
  declNames.toArray.mapM fun declName => do
    `(Parser.Tactic.grindParam| = $(← toIdent declName))

private def mkGrindStx (info : Try.Info) : MetaM (TSyntax `tactic) := do
  let grind ← `(tactic| grind?)
  let mut tacs := #[grind]
  unless info.eqnCandidates.isEmpty do
    tacs := tacs.push (setGrindParams grind (← mkGrindEqnParams info.eqnCandidates))
  unless info.unfoldCandidates.isEmpty do
    tacs := tacs.push (setGrindParams grind (← mkGrindEqnParams info.unfoldCandidates))
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
  let tacs ← info.funIndCandidates.toArray.mapM (mkFunIndStx · cont)
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
  | `(tactic| try?%$tk $config:optConfig) => focus do withMainContext do
    let config ← elabTryConfig config
    let info ← Try.collect (← getMainGoal) config
    let stx ← mkTryEvalSuggestStx info
    evalAndSuggest tk stx
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
