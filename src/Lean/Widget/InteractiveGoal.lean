/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Meta.PPGoal
import Lean.Widget.InteractiveCode

/-! RPC procedures for retrieving tactic and term goals with embedded `CodeWithInfos`. -/

namespace Lean.Widget
open Server

structure InteractiveHypothesis where
  names : Array String
  ids : Array String
  type : CodeWithInfos
  val? : Option CodeWithInfos := none
  isInstance : Bool
  isType : Bool
  /-- Identifies the group of hypotheses.
  Used as a React key and to unambiguously
  address the hypothesis group in callbacks.-/
  key : String
  deriving Inhabited, RpcEncoding

structure InteractiveGoal where
  hyps      : Array InteractiveHypothesis
  type      : CodeWithInfos
  userName? : Option String
  goalPrefix : String
  /-- Identifies the goal (ie with the unique
  name of the MVar that it is a goal for.)
  [todo] what should the key be for a term goal?-/
  key? : Option String := none
  deriving Inhabited, RpcEncoding

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
    match hyp.names.toList with
    | [] =>
      ret := ret ++ Format.group f!":{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
    | _ =>
      let names := " ".intercalate hyp.names.toList
      match hyp.val? with
      | some val =>
        ret := ret ++ Format.group f!"{names} : {hyp.type.stripTags} :={Format.nest indent (Format.line ++ val.stripTags)}"
      | none =>
        ret := ret ++ Format.group f!"{names} :{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
  ret := addLine ret
  ret ++ f!"{g.goalPrefix}{Format.nest indent g.type.stripTags}"

end InteractiveGoal

structure InteractiveTermGoal where
  hyps      : Array InteractiveHypothesis
  type      : CodeWithInfos
  range     : Lsp.Range
  deriving Inhabited, RpcEncoding

namespace InteractiveTermGoal

def toInteractiveGoal (g : InteractiveTermGoal) : InteractiveGoal :=
  { g with userName? := none, goalPrefix := "⊢ " }

end InteractiveTermGoal

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving RpcEncoding

open Meta in
def addInteractiveHypothesis (hyps : Array InteractiveHypothesis) (ids : Array (Name × FVarId)) (type : Expr) (value? : Option Expr := none) : MetaM (Array InteractiveHypothesis) := do
  if ids.size == 0 then
    throwError "Can only add a nonzero number of ids as an InteractiveHypothesis."
  let fvarIds := ids.map (toString ∘ FVarId.name ∘ Prod.snd)
  return hyps.push {
    names      := ids.map (toString ∘ Prod.fst)
    ids        := fvarIds
    type       := (← ppExprTagged type)
    val?       := (← value?.mapM ppExprTagged)
    isInstance := (← isClass? type).isSome
    isType     := (← instantiateMVars type).isSort
    key := fvarIds[0]
  }

open Meta in
/-- A variant of `Meta.ppGoal` which preserves subexpression information for interactivity. -/
def goalToInteractive (mvarId : MVarId) : MetaM InteractiveGoal := do
  let some mvarDecl := (← getMCtx).findDecl? mvarId
    | throwError "unknown goal {mvarId.name}"
  let ppAuxDecls := pp.auxDecls.get (← getOptions)
  let lctx := mvarDecl.lctx
  let lctx : LocalContext := lctx.sanitizeNames.run' { options := (← getOptions) }
  withLCtx lctx mvarDecl.localInstances do
    let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
    -- The following two `let rec`s are being used to control the generated code size.
    -- They should be removed after we rewrite the compiler in Lean
    let pushPending (ids : Array (Name × FVarId)) (type? : Option Expr) (hyps : Array InteractiveHypothesis)
        : MetaM (Array InteractiveHypothesis) :=
      if ids.isEmpty then
        pure hyps
      else
        match type? with
        | none      => pure hyps
        | some type => addInteractiveHypothesis hyps ids type
    let mut varNames : Array (Name × FVarId) := #[]
    let mut prevType? : Option Expr := none
    let mut hyps : Array InteractiveHypothesis := #[]
    for localDecl in lctx do
      if !ppAuxDecls && localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
        pure ()
      else
        if hiddenProp.contains localDecl.fvarId then
          -- localDecl has an inaccessible name and
          -- is a proposition containing "visible" names.
          let type ← instantiateMVars localDecl.type
          hyps ← pushPending varNames prevType? hyps
          hyps ← addInteractiveHypothesis hyps #[(Name.anonymous, localDecl.fvarId)] type
          varNames := #[]
          prevType? := none
        else
          match localDecl with
          | LocalDecl.cdecl index fvarId varName type _   =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            prevType? := some type
            if prevType? == none || prevType? == some type then
              varNames := varNames.push (varName, fvarId)
            else
              hyps ← pushPending varNames prevType? hyps
              varNames := #[(varName, fvarId)]
          | LocalDecl.ldecl index fvarId varName type val _ => do
            let varName := varName.simpMacroScopes
            hyps ← pushPending varNames prevType? hyps
            let type ← instantiateMVars type
            let val ← instantiateMVars val
            hyps ← addInteractiveHypothesis hyps #[(varName, fvarId)] type val
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
      key? := some mvarId.name.toString
    }

end Lean.Widget
