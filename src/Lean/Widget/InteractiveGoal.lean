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
  type : CodeWithInfos
  val? : Option CodeWithInfos := none
  deriving Inhabited, RpcEncoding

structure InteractiveGoal where
  hyps      : Array InteractiveHypothesis
  type      : CodeWithInfos
  userName? : Option String
  deriving Inhabited, RpcEncoding

namespace InteractiveGoal

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line

def pretty (g : InteractiveGoal) : Format := do
  let indent := 2 -- Use option
  let mut ret := match g.userName? with
    | some userName => f!"case {userName}"
    | none          => Format.nil
  for hyp in g.hyps do
    ret := addLine ret
    let names := " ".intercalate hyp.names.toList
    match hyp.val? with
    | some val =>
      ret := ret ++ Format.group f!"{names} : {hyp.type.stripTags} :={Format.nest indent (Format.line ++ val.stripTags)}"
    | none =>
      ret := ret ++ Format.group f!"{names} :{Format.nest indent (Format.line ++ hyp.type.stripTags)}"
  ret := addLine ret
  ret ++ f!"⊢ {Format.nest indent g.type.stripTags}"

end InteractiveGoal

structure InteractiveTermGoal where
  hyps      : Array InteractiveHypothesis
  type      : CodeWithInfos
  range     : Lsp.Range
  deriving Inhabited, RpcEncoding

namespace InteractiveTermGoal

def toInteractiveGoal (g : InteractiveTermGoal) : InteractiveGoal :=
  { g with userName? := none }

end InteractiveTermGoal

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving RpcEncoding

open Meta in
/-- A variant of `Meta.ppGoal` which preserves subexpression information for interactivity. -/
def goalToInteractive (mvarId : MVarId) : MetaM InteractiveGoal := do
  let some mvarDecl ← (← getMCtx).findDecl? mvarId
    | throwError "unknown goal {mvarId.name}"
  let ppAuxDecls := pp.auxDecls.get (← getOptions)
  let lctx := mvarDecl.lctx
  let lctx := lctx.sanitizeNames.run' { options := (← getOptions) }
  withLCtx lctx mvarDecl.localInstances do
    let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
    -- The following two `let rec`s are being used to control the generated code size.
    -- Then should be remove after we rewrite the compiler in Lean
    let rec pushPending (ids : Array Name) (type? : Option Expr) (hyps : Array InteractiveHypothesis)
        : MetaM (Array InteractiveHypothesis) :=
      if ids.isEmpty then
        pure hyps
      else
        match ids, type? with
        | _,  none      => pure hyps
        | _,  some type =>
          return hyps.push { names := ids.map toString, type := ← exprToInteractive type }
    let rec ppVars (varNames : Array Name) (prevType? : Option Expr) (hyps : Array InteractiveHypothesis) (localDecl : LocalDecl)
       : MetaM (Array Name × Option Expr × Array InteractiveHypothesis) := do
      if hiddenProp.contains localDecl.fvarId then
        let hyps ← pushPending varNames prevType? hyps
        let type ← instantiateMVars localDecl.type
        let hyps := hyps.push { names := #[], type := ← exprToInteractive type }
        pure (#[], none, hyps)
      else
        match localDecl with
        | LocalDecl.cdecl _ _ varName type _   =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            pure (varNames.push varName, some type, hyps)
          else do
            let hyps ← pushPending varNames prevType? hyps
            pure (#[varName], some type, hyps)
        | LocalDecl.ldecl _ _ varName type val _ => do
          let varName := varName.simpMacroScopes
          let hyps ← pushPending varNames prevType? hyps
          let type ← instantiateMVars type
          let val ← instantiateMVars val
          let typeFmt ← exprToInteractive type
          let valFmt ← exprToInteractive val
          let hyps := hyps.push { names := #[toString varName], type := typeFmt, val? := valFmt }
          pure (#[], none, hyps)
    let (varNames, type?, hyps) ← lctx.foldlM (init := (#[], none, #[]))
      fun (varNames, prevType?, hyps) (localDecl : LocalDecl) =>
        if !ppAuxDecls && localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
          pure (varNames, prevType?, hyps)
        else
          ppVars varNames prevType? hyps localDecl
    let hyps ← pushPending varNames type? hyps
    let goalTp ← instantiateMVars mvarDecl.type
    let goalFmt ← exprToInteractive goalTp
    let userName? := match mvarDecl.userName with
      | Name.anonymous => none
      | name           => some <| toString name.eraseMacroScopes
    return { hyps, type := goalFmt, userName? }

end Lean.Widget
