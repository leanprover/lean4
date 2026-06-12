/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Elab.Do.Basic
meta import Lean.Parser.Do
import Lean.Elab.Do.Control
import Lean.Elab.Do.InferControlInfo
import Lean.Elab.Binders

namespace Lean.Elab.Do

open Lean.Parser.Term
open Lean.Meta

@[builtin_term_elab Lean.Parser.Term.doForward]
public def elabDoForward : Term.TermElab := fun _ _ =>
  throwError "\
    `do←` may only appear as the last argument of a function application \
    inside an enclosing `do` block, optionally inside a `fun` binder"

private def forwardHint (headApp : Term) (reason : MessageData) : MessageData :=
  m!"\
    `{headApp}` is not a valid `do←` wrapper: {reason}. The wrapper must have type \
    `(… → m α) → m α` for some `α` that is universally quantified in the wrapper's signature and \
    does not appear elsewhere."

/--
Check that `probeExpr` (the elaboration of `headApp ?forwarded`) has the shape required for
`do←`: its result type is `m α` for an unassigned `α`, the `forwarded` slot is `… → m α` with
the same `α` (and `α` not occurring in the slot's input types), and `α` does not occur in any
*other* explicit argument of the elaborated probe.
-/
private def validateForwarder (headApp : Term) (forwarded probeExpr : Expr) : MetaM Unit := do
  let reject {α} (reason : MessageData) : MetaM α := throwError forwardHint headApp reason
  let probeType ← whnfD (← instantiateMVars (← inferType probeExpr))
  let .app _ alphaRet := probeType
    | reject m!"its return type `{probeType}` is not of the form `m α`"
  unless alphaRet.isMVar do
    reject m!"its return type pins `α` to a concrete type"
  let argMentionsAlpha (arg : Expr) : MetaM (Option Expr) := do
    let ty ← inferType arg
    if (← instantiateMVars ty).findMVar? (· == alphaRet.mvarId!) |>.isSome then
      return some ty
    else return none
  forallTelescopeReducing (← inferType forwarded) fun args body => do
    unless ← isDefEq probeType (← whnfD (← instantiateMVars body)) do
      reject m!"the forwarded body's `α` differs from the wrapper's return `α`"
    for arg in args do
      if let some ty ← argMentionsAlpha arg then
        reject m!"`α` appears in the forwarded body's input type `{ty}`"
  forallTelescopeReducing (← inferType probeExpr.getAppFn) fun fvars _ => do
    for (fvar, appArg) in fvars.zip probeExpr.getAppArgs do
      unless (← fvar.fvarId!.getDecl).binderInfo matches .default do continue
      let appArgInst ← instantiateMVars appArg
      if appArgInst == forwarded then continue
      if let some ty ← argMentionsAlpha appArgInst then
        reject m!"`α` appears in an applied explicit argument of type `{ty}`"

/--
Elaborate `e` as an application whose last argument is a `do←` body, performing the effect
forwarding. Returns `none` if `e` doesn't have that shape.

Strategy: build `headApp ?forwarded` with a fresh metavariable in the body slot and elaborate
it. Lean's elaborator handles named args, defaults, and dot notation. We then check the
wrapper's shape against the probe; on success, the lifted body is assigned into `?forwarded`
and the probe expression itself is the result.
-/
public def tryElabForwardApp? (e : Term) (dec : DoElemCont) : DoElabM (Option Expr) := do
  let some (headApp, arg) := Forward.matchApp? e | return none
  let (forwarded, probeExpr) ← controlAtTermElabM fun _ => withFreshMacroScope do
    let forwardedStx ← `(?forwarded)
    let forwarded ← Term.elabTerm forwardedStx none
    let probeExpr ← Term.elabTerm (← `($headApp $forwardedStx)) none
    pure (forwarded, probeExpr)
  validateForwarder headApp forwarded probeExpr
  let bodyInfo ← InferControlInfo.ofSeq arg.body
  let forwarder ← EffectForwarder.ofCont bodyInfo dec
  let liftedBody ← controlAtTermElabM fun runInBase => do
    Term.elabFunBinders (arg.binders.map (·.raw)) none fun bsExpr _ => runInBase do
      mkLambdaFVars bsExpr (← forwarder.lift (elabDoSeq arg.body))
  unless ← forwarded.mvarId!.checkedAssign liftedBody do
    throwError "the lifted body's type does not match the wrapper's body slot type"
  -- NB: No `withDeadCode` wrap on `restoreCont`'s result, because it is unclear whether `body` is
  --     even called.
  return some (← (← forwarder.restoreCont).mkBindUnlessPure probeExpr)

end Lean.Elab.Do
