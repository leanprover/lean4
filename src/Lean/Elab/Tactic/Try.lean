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

namespace Lean.Elab.Tactic
open Meta
/-!
A **very** simple `try?` tactic implementation.
-/

declare_config_elab elabTryConfig Try.Config

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
