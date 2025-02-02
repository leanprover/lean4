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

open Meta.Tactic in
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

private def evalTryTraceCore : M Unit := do
  if (← trySimp) then return ()
  if (← trySimpArith) then return ()
  if (← tryGrind) then return ()
  Meta.throwTacticEx `«try?» (← read).mvarId "`try?` failed, consider using `grind` manually"

@[builtin_tactic Lean.Parser.Tactic.tryTrace] def evalTryTrace : Tactic := fun stx => do
  match stx with
  | `(tactic| try?%$tk $config:optConfig) =>
    let mvarId ← getMainGoal
    let config ← elabTryConfig config
    evalTryTraceCore { config, tk, mvarId }
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
