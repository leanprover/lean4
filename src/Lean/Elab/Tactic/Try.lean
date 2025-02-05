/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Try
import Init.Grind.Tactics
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
  | `(tactic| grind? $config:optConfig $[only%$only]?  $[ [$params:grindParam,*] ]? $[on_failure $fallback?]?) =>
    let trace ← evalGrindCore tac config only params fallback? true
    mkGrindOnly config fallback? trace
  | _ => throwUnsupportedSyntax

private def evalSuggestSimpTrace (tac : TSyntax `tactic) : TacticM (TSyntax `tactic) := withMainContext do
  match tac with
  | `(tactic| simp? $_:optConfig $[only%$only]? $[[$args,*]]? $(loc)?) =>
    let tac ← simpTraceToSimp tac
    let { ctx, simprocs, .. } ← mkSimpContext tac (eraseLocal := false)
    let stats ← simpLocation ctx (simprocs := simprocs) none <| (loc.map expandLocation).getD (.targets #[] true)
    mkSimpCallStx tac stats.usedTheorems
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

-- TODO: rewrite the following code using `evalSuggest`

structure Try.Context where
  mvarId : MVarId
  config : Try.Config
  tk     : Syntax

private abbrev M := ReaderT Try.Context TacticM

instance : OrElse (M α) where
  orElse a b := fun ctx => a ctx <|> b () ctx

open Tactic in
private def addSuggestion (stx : TryThis.Suggestion) : M Bool := do
  TryThis.addSuggestion (← read).tk stx (origSpan? := (← getRef))
  return true

-- TODO: vanilla `induction`.
-- TODO: cleanup the whole file, and use better combinators
-- TODO: make it extensible.
-- TODO: librarySearch integration.
-- TODO: premise selection.

private def failed (msg : MessageData) : M Bool := do
  trace[«try»] msg
  return false

private def tryTac (stx : TSyntax `tactic) (msg : MessageData) : M Bool :=
  (do
    focusAndDone <| evalTactic stx
    addSuggestion stx)
  <|> failed msg

private def trySimp : M Bool := do
  tryTac (← `(tactic| simp)) "`simp` failed"

set_option hygiene false in
private def trySimpArith : M Bool := do
  tryTac (← `(tactic| simp +arith)) "`simp +arith` failed"

private def tryGrind : M Bool := do
  (do
    evalTactic (← `(tactic| grind -verbose))
    addSuggestion (← `(tactic| grind?)))
  <|> failed "`grind` failed"

private def collect : M Try.Info := do
  Try.collect (← read).mvarId (← read).config

private def toIdent (declName : Name) : MetaM Ident := do
  return mkIdent (← unresolveNameGlobalAvoidingLocals declName)

inductive TacticKind where
  | exec
  | suggestion
  | error

private def mkGrindStx (params : Array (TSyntax ``Parser.Tactic.grindParam)) (kind : TacticKind) : MetaM (TSyntax `tactic) := do
  let result ← match kind with
    | .exec => `(tactic| grind -verbose)
    | .suggestion => `(tactic| grind?)
    | .error => `(tactic| grind)
  if params.isEmpty then
    return result
  else
    let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
    return ⟨result.raw.setArg 3 (mkNullNode paramsStx)⟩

private def mkGrindEqnsStx (declNames : Std.HashSet Name) : M (TacticKind → MetaM (TSyntax `tactic)) := do
  let mut params := #[]
  for declName in declNames do
    params := params.push (← `(Parser.Tactic.grindParam| = $(← toIdent declName)))
  return mkGrindStx params

private def tryTac' (mkTac : TacticKind → MetaM (TSyntax `tactic)) : M Bool := do
  let stx ← mkTac .exec
  (do
    focusAndDone <| evalTactic stx
    addSuggestion (← mkTac .suggestion))
  <|>
  (do failed m!"`{← mkTac .error}` failed")

private def tryGrindEqns (info : Try.Info) : M Bool := do
  if info.eqnCandidates.isEmpty then return false
  tryTac' (← mkGrindEqnsStx info.eqnCandidates)

private def tryGrindUnfold (info : Try.Info) : M Bool := do
  if info.unfoldCandidates.isEmpty then return false
  tryTac' (← mkGrindEqnsStx info.unfoldCandidates)

private def allAccessible (majors : Array FVarId) : MetaM Bool :=
  majors.allM fun major => do
    let localDecl ← major.getDecl
    -- TODO: we are not checking shadowed variables
    return !localDecl.userName.hasMacroScopes

open Try.Collector in
private partial def tryFunIndsCore (info : Try.Info) (mkBody : TacticKind → MetaM (TSyntax `tactic)) : M Bool := do
  go info.funIndCandidates.toList
where
  go' (c : FunIndCandidate) : M Bool := do
    if (← allAccessible c.majors) then
      let mut terms := #[]
      for major in c.majors do
        let localDecl ← major.getDecl
        terms := terms.push (← `($(mkIdent localDecl.userName):term))
      let indFn ← toIdent c.funIndDeclName
      tryTac' fun k => do
        let body ← mkBody k
        `(tactic| induction $terms,* using $indFn <;> $body)
    else
      -- TODO: use `rename_i`
      failed "`induction` failed, majors contain inaccessible vars {c.majors.map mkFVar}"

  go (cs : List FunIndCandidate) : M Bool := do
    match cs with
    | [] => return false
    | c::cs =>
      trace[try.debug.funInd] "{c.funIndDeclName}, {c.majors.map mkFVar}"
      go' c <||> go cs

private partial def tryFunIndsGrind (info : Try.Info) : M Bool :=
  tryFunIndsCore info (mkGrindStx #[])

private partial def tryFunIndsGrindEqns (info : Try.Info) : M Bool := do
  if info.eqnCandidates.isEmpty then return false
  tryFunIndsCore info (← mkGrindEqnsStx info.eqnCandidates)

private def evalTryTraceCore : M Unit := do
  if (← trySimp) then return ()
  if (← trySimpArith) then return ()
  if (← tryGrind) then return ()
  let info ← collect
  if (← tryGrindEqns info) then return ()
  if (← tryGrindUnfold info) then return ()
  if (← tryFunIndsGrind info) then return ()
  if (← tryFunIndsGrindEqns info) then return ()
  Meta.throwTacticEx `«try?» (← read).mvarId "consider using `grind` manually, `set_option trace.try true` shows everything `try?` tried"

@[builtin_tactic Lean.Parser.Tactic.tryTrace] def evalTryTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| try?%$tk $config:optConfig) =>
    let mvarId ← getMainGoal
    let config ← elabTryConfig config
    evalTryTraceCore { config, tk, mvarId }
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
