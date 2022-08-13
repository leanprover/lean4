/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Meta.PPGoal
import Lean.Widget.InteractiveCode
import Lean.Data.Lsp.Extra

/-! RPC procedures for retrieving tactic and term goals with embedded `CodeWithInfos`. -/

namespace Lean.Widget
open Server

structure InteractiveHypothesisBundle where
  /-- The user-friendly name for each hypothesis.
  If anonymous then the name is inaccessible and hidden. -/
  names : Array Name
  fvarIds : Array FVarId
  type : CodeWithInfos
  val? : Option CodeWithInfos := none
  isInstance : Bool
  isType : Bool
  deriving Inhabited, RpcEncodable

structure InteractiveGoal where
  hyps      : Array InteractiveHypothesisBundle
  type      : CodeWithInfos
  userName? : Option String
  goalPrefix : String
  /-- Identifies the goal (ie with the unique
  name of the MVar that it is a goal for.)
  This is none when we are showing a term goal. -/
  mvarId? : Option MVarId := none
  deriving Inhabited, RpcEncodable

namespace InteractiveGoal

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line

def pretty (g : InteractiveGoal) : Format := Id.run do
  let indent := 2 -- Use option
  let mut ret := match g.userName? with
    | some userName => f!"case {userName}"
    | none          => Format.nil
  for hyp in g.hyps do
    ret := addLine ret
    let names := hyp.names
        |>.toList
        |>.filter (not ∘ Name.isAnonymous)
        |>.map toString
        |> " ".intercalate
    match names with
    | "" =>
      ret := ret ++ Format.group f!":{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
    | _ =>
      match hyp.val? with
      | some val =>
        ret := ret ++ Format.group f!"{names} : {hyp.type.stripTags} :={Format.nest indent (Format.line ++ val.stripTags)}"
      | none =>
        ret := ret ++ Format.group f!"{names} :{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
  ret := addLine ret
  ret ++ f!"{g.goalPrefix}{Format.nest indent g.type.stripTags}"

end InteractiveGoal

structure InteractiveTermGoal where
  hyps      : Array InteractiveHypothesisBundle
  type      : CodeWithInfos
  range     : Lsp.Range
  deriving Inhabited, RpcEncodable

namespace InteractiveTermGoal

def toInteractiveGoal (g : InteractiveTermGoal) : InteractiveGoal :=
  { g with userName? := none, goalPrefix := "⊢ " }

end InteractiveTermGoal

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving RpcEncodable

open Meta in
def addInteractiveHypothesisBundle (hyps : Array InteractiveHypothesisBundle) (ids : Array (Name × FVarId)) (type : Expr) (value? : Option Expr := none) : MetaM (Array InteractiveHypothesisBundle) := do
  if ids.size == 0 then
    throwError "Can only add a nonzero number of ids as an InteractiveHypothesisBundle."
  let fvarIds := ids.map Prod.snd
  let names := ids.map Prod.fst
  return hyps.push {
    names      := names
    fvarIds    := fvarIds
    type       := (← ppExprTagged type)
    val?       := (← value?.mapM ppExprTagged)
    isInstance := (← isClass? type).isSome
    isType     := (← instantiateMVars type).isSort
  }

open Meta in
/-- A variant of `Meta.ppGoal` which preserves subexpression information for interactivity. -/
def goalToInteractive (mvarId : MVarId) : MetaM InteractiveGoal := do
  let some mvarDecl := (← getMCtx).findDecl? mvarId
    | throwError "unknown goal {mvarId.name}"
  let ppAuxDecls := pp.auxDecls.get (← getOptions)
  let showLetValues := pp.showLetValues.get (← getOptions)
  let lctx := mvarDecl.lctx
  let lctx : LocalContext := lctx.sanitizeNames.run' { options := (← getOptions) }
  withLCtx lctx mvarDecl.localInstances do
    let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
    let pushPending (ids : Array (Name × FVarId)) (type? : Option Expr) (hyps : Array InteractiveHypothesisBundle)
        : MetaM (Array InteractiveHypothesisBundle) :=
      if ids.isEmpty then
        pure hyps
      else
        match type? with
        | none      => pure hyps
        | some type => addInteractiveHypothesisBundle hyps ids type
    let mut varNames : Array (Name × FVarId) := #[]
    let mut prevType? : Option Expr := none
    let mut hyps : Array InteractiveHypothesisBundle := #[]
    for localDecl in lctx do
      if !ppAuxDecls && localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
        continue
      else
        if hiddenProp.contains localDecl.fvarId then
          -- localDecl has an inaccessible name and
          -- is a proposition containing "visible" names.
          let type ← instantiateMVars localDecl.type
          hyps ← pushPending varNames prevType? hyps
          hyps ← addInteractiveHypothesisBundle hyps #[(Name.anonymous, localDecl.fvarId)] type
          varNames := #[]
          prevType? := none
        else
          match localDecl with
          | LocalDecl.cdecl _index fvarId varName type _   =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            if prevType? == none || prevType? == some type then
              varNames := varNames.push (varName, fvarId)
            else
              hyps ← pushPending varNames prevType? hyps
              varNames := #[(varName, fvarId)]
            prevType? := some type
          | LocalDecl.ldecl _index fvarId varName type val _ => do
            let varName := varName.simpMacroScopes
            hyps ← pushPending varNames prevType? hyps
            let type ← instantiateMVars type
            let val? ← if showLetValues then pure (some (← instantiateMVars val)) else pure none
            hyps ← addInteractiveHypothesisBundle hyps #[(varName, fvarId)] type val?
            varNames := #[]
            prevType? := none
    hyps ← pushPending varNames prevType? hyps
    let goalTp ← instantiateMVars mvarDecl.type
    let goalFmt ← ppExprTagged goalTp
    let userName? := match mvarDecl.userName with
      | Name.anonymous => none
      | name           => some <| toString name.eraseMacroScopes
    return {
      hyps,
      type := goalFmt,
      userName?,
      goalPrefix := getGoalPrefix mvarDecl,
      mvarId? := some mvarId
    }

end Lean.Widget
