/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Unfold
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

def unfoldLocalDecl (declName : Name) (fvarId : FVarId) : TacticM Unit := do
  replaceMainGoal [← Meta.unfoldLocalDecl (← getMainGoal) fvarId declName]

def unfoldTarget (declName : Name) : TacticM Unit := do
  replaceMainGoal [← Meta.unfoldTarget (← getMainGoal) declName]

def zetaDeltaLocalDecl (declFVarId : FVarId) (fvarId : FVarId) : TacticM Unit := do
  replaceMainGoal [← Meta.zetaDeltaLocalDecl (← getMainGoal) fvarId declFVarId]

def zetaDeltaTarget (declFVarId : FVarId) : TacticM Unit := do
  replaceMainGoal [← Meta.zetaDeltaTarget (← getMainGoal) declFVarId]

/-- "unfold " ident+ (location)? -/
@[builtin_tactic Lean.Parser.Tactic.unfold] def evalUnfold : Tactic := fun stx => do
  let loc := expandOptLocation stx[2]
  for declNameId in stx[1].getArgs do
    go declNameId loc
where
  go (declNameId : Syntax) (loc : Location) : TacticM Unit := withMainContext <| withRef declNameId do
    let e ← withoutRecover <| elabTermForApply declNameId (mayPostpone := false)
    match e with
    | .const declName _ =>
      withLocation loc (unfoldLocalDecl declName) (unfoldTarget declName) (throwTacticEx `unfold · m!"did not unfold '{declName}'")
    | .fvar declFVarId =>
      unless ← declFVarId.isLetVar do
        throwError "tactic 'unfold' failed, local variable '{Expr.fvar declFVarId}' has no definition"
      withLocation loc (zetaDeltaLocalDecl declFVarId) (zetaDeltaTarget declFVarId) (throwTacticEx `unfold · m!"did not unfold '{e}'")
    | _ => throwTacticEx `unfold (← getMainGoal) m!"expression {e} is not a global or local constant"

end Lean.Elab.Tactic
