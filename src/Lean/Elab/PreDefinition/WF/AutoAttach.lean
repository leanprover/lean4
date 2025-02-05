/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
prelude
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Elab.Tactic.Simp

open Lean Meta

register_builtin_option wf.auto_attach : Bool := {
  defValue := true
  descr := "pre-process definitions defined by well-founded recursion with the `auto_attach` simp set"
}

namespace Lean.Elab.WF

builtin_initialize autoAttachSimpExtension : SimpExtension ←
  registerSimpAttr `auto_attach
    "simp lemma used in the preprocessing of well-founded recursive function definitions, in \
    particular to add additional hypotheses to the context. Also see `wfParam`."

private def getSimpContext : MetaM Simp.Context := do
  let simpTheorems ← autoAttachSimpExtension.getTheorems
  Simp.mkContext
    (simpTheorems  := #[simpTheorems])
    (congrTheorems := {})
    (config        := { Simp.neutralConfig with dsimp := false })

def isWfParam? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``wfParam 2 then
    e.appArg!
  else
    none

def mkWfParam (e : Expr) : MetaM Expr :=
  mkAppM ``wfParam #[e]

/-- `f (wfParam x) ==> wfParam (f x)` if `f` is a projection -/
builtin_dsimproc paramProj (_) := fun e => do
  if h : e.isApp then
    let some a' := isWfParam? (e.appArg h) | return .continue
    let f := e.getAppFn
    unless f.isConst do return .continue
    unless (← isProjectionFn f.constName!) do return .continue
    let e' ← mkWfParam (.app (e.appFn h) a')
    return .done e'
  else
    return .continue

/-- `match (wfParam x) with con y => alt[y] ==> match x with con y => alt[wfParam y] -/
builtin_dsimproc paramMatcher (_) := fun e => do
  let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true)  | return .continue
  unless matcherApp.discrs.any (isWfParam? · |>.isSome) do return .continue
  let discrs' := matcherApp.discrs.map (fun e => isWfParam? e |>.getD e)
  let alts' ← matcherApp.alts.mapM fun alt =>
    lambdaTelescope alt fun xs body => do
      -- Annotate all xs with `wfParam`
      let xs' ← xs.mapM (mkWfParam ·)
      let body' := body.replaceFVars xs xs'
      mkLambdaFVars xs body'
  let matcherApp' := { matcherApp with discrs := discrs', alts := alts' }
  return .continue <| matcherApp'.toExpr


def autoAttach (e : Expr) : MetaM Simp.Result := do
  unless wf.auto_attach.get (← getOptions) do
    return { expr := e }
  lambdaTelescope e fun xs e => do
    -- Annotate all xs with `wfParam`
    let xs' ← xs.mapM mkWfParam
    let e' := e.replaceFVars xs xs'

    -- Now run the simplifier
    let simprocs : Simprocs := {}
    let simprocs ← simprocs.add ``paramProj (post := true)
    let simprocs ← simprocs.add ``paramMatcher (post := false)
    let (result, _) ← Meta.simp e' (← getSimpContext) (simprocs := #[simprocs])

    -- Remove left-over markers
    let e'' ← Core.transform result.expr fun e =>
      e.withApp fun f as => do
        if f.isConstOf ``wfParam then
          if h : as.size ≥ 2 then
            return .continue (mkAppN as[1] as[2:])
        return .continue
    let result ← result.mkEqTrans { expr := e'', proof? := none }

    trace[Elab.definition.wf] "Attach-introduction:{indentExpr e}\nto{indentExpr e'}\ncleaned up as{indentExpr e''}"
    result.addLambdas xs

end Lean.Elab.WF
