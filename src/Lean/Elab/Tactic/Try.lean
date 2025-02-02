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

inductive GrindKind where
  | tactic
  | suggestion
  | errorMsg

private def mkGrindStx (params : Array (TSyntax ``Parser.Tactic.grindParam)) (kind : GrindKind := .tactic) : MetaM (TSyntax `tactic) := do
  let result ← match kind with
    | .tactic => `(tactic| grind -verbose)
    | .suggestion => `(tactic| grind?)
    | .errorMsg => `(tactic| grind)
  let paramsStx := #[mkAtom "[", (mkAtom ",").mkSep params, mkAtom "]"]
  return ⟨result.raw.setArg 3 (mkNullNode paramsStx)⟩

private def tryGrindWith (params : Array (TSyntax ``Parser.Tactic.grindParam)) : M Bool := do
  let stx ← mkGrindStx params
  (do
    evalTactic stx
    addSuggestion (← mkGrindStx params .suggestion))
  <|>
  (do failed m!"`{← mkGrindStx params .errorMsg}` failed")

private def tryGrindEqnsCore (declNames : Std.HashSet Name) : M Bool := do
  if declNames.isEmpty then return false
  let mut params := #[]
  for declName in declNames do
    params := params.push (← `(Parser.Tactic.grindParam| = $(← toIdent declName)))
  tryGrindWith params

private def tryGrindEqns (info : Try.Info) : M Bool := do
  tryGrindEqnsCore info.eqnCandidates

private def tryGrindUnfold (info : Try.Info) : M Bool := do
  tryGrindEqnsCore info.unfoldCandidates

private def evalTryTraceCore : M Unit := do
  if (← trySimp) then return ()
  if (← trySimpArith) then return ()
  if (← tryGrind) then return ()
  let info ← collect
  if (← tryGrindEqns info) then return ()
  if (← tryGrindUnfold info) then return ()
  Meta.throwTacticEx `«try?» (← read).mvarId "consider using `grind` manually"

@[builtin_tactic Lean.Parser.Tactic.tryTrace] def evalTryTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| try?%$tk $config:optConfig) =>
    let mvarId ← getMainGoal
    let config ← elabTryConfig config
    evalTryTraceCore { config, tk, mvarId }
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
