/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Transform
import Lean.Meta.Match.MatcherApp.Basic
import Lean.Elab.Tactic.Simp

open Lean Meta

namespace Lean.Elab.WF

def getAttachSimpTheorems : MetaM SimpTheorems := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``dite_eq_ite (inv := true)
  -- let s ← s.addConst `List.wfParam_to_attach
  -- let s ← s.addConst `Array.wfParam_to_attach
  let s ← s.addConst `List.map_wfParam
  let s ← s.addConst `List.map_unattach
  let s ← s.addConst `List.filter_wfParam
  let s ← s.addConst `List.filter_unattach
  let s ← s.addConst `List.reverse_wfParam
  let s ← s.addConst `List.reverse_unattach
  let s ← s.addConst `List.foldl_wfParam
  let s ← s.addConst `List.foldl_unattach
  let s ← s.addConst `Array.map_wfParam
  let s ← s.addConst `Array.map_unattach
  pure s

def getUnattachSimpTheorems : MetaM SimpTheorems := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``List.unattach_attach
  let s ← s.addConst ``List.map_subtype
  let s ← s.addConst ``List.unattach_filter
  let s ← s.addConst ``List.unattach_reverse
  let s ← s.addConst `List.unattach_foldl
  let s ← s.addConst ``Array.map_subtype
  let s ← s.addConst ``Array.unattach_attach
  pure s

private def getSimpContext : MetaM Simp.Context := do
  Simp.mkContext
    (simpTheorems  := #[(← getAttachSimpTheorems)])
    (congrTheorems := {})
    (config        := { Simp.neutralConfig with dsimp := false })

private def getCleanupSimpContext : MetaM Simp.Context := do
  let s : SimpTheorems := {}
  let s ← s.addConst ``List.unattach_attach
  let s ← s.addConst ``Array.unattach_attach
  let s ← s.addDeclToUnfold ``wfParam
  Simp.mkContext
    (simpTheorems  := #[s])
    (congrTheorems := {})
    (config        := { Simp.neutralConfig with dsimp := true })

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


def iteToDIte (e : Expr) : MetaM Expr := do
  lambdaTelescope e fun xs e => do
    -- Annotate all xs with `wfParam`
    let xs' ← xs.mapM mkWfParam
    let e' := e.replaceFVars xs xs'

    -- Now run the simplifier
    let simprocs : Simprocs := {}
    let simprocs ← simprocs.add ``paramProj (post := true)
    let simprocs ← simprocs.add ``paramMatcher (post := false)
    let (result, _) ← Meta.simp e' (← getSimpContext) (simprocs := #[simprocs])
    let e' := result.expr

    -- Remove markers
    -- let (result, _) ← Meta.simp e' (← getCleanupSimpContext)
    -- let e'' := result.expr
    -- Simp, even with dsimp on, is not as thorough as `Core.transform`:
    let e'' ← Core.transform e' fun e =>
      e.withApp fun f as => do
        if f.isConstOf ``wfParam then
          if h : as.size ≥ 2 then
            return .continue (mkAppN as[1] as[2:])
        return .continue

    trace[Elab.definition.wf] "Attach-introduction:{indentExpr e}\nto{indentExpr e'}\ncleaned up as{indentExpr e''}"

    mkLambdaFVars xs e''

/-
run_elab do
  let stx ← `(fun (n : Nat) => if n > 0 then 3 else 4)
  let e ← Elab.Term.elabTerm stx .none
  let e' ← iteToDIte e
  logInfo m!"{e}\n{e'}"
-/


end Lean.Elab.WF
