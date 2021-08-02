/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Widget.ExprWithCtx

/-! RPC procedures for retrieving tactic and term goals with embedded `ExprText`s. -/
-- TODO(WN): this module is mostly a slightly adapted copy of the corresponding `plainGoal/plainTemGoal` handlers
-- unify them somehow? or delete the plain ones.

namespace Lean.Widget
open Server

structure InteractiveGoal where
  hyps      : Array (String × ExprText)
  type      : ExprText
  userName? : Option String
  deriving RpcEncoding

structure InteractiveGoals where
  goals : Array InteractiveGoal
  deriving RpcEncoding

open Meta in
def goalToInteractive (mvarId : MVarId) : MetaM InteractiveGoal := do
  match (← getMCtx).findDecl? mvarId with
  | none          => unreachable!
  | some mvarDecl => do
    let indent         := 2 -- Use option
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    -- tmp so (← ) lifts work
    let tmpExprWithCtx : ExprWithCtx := {
        lctx
        mctx := ← getMCtx
        options := ← getOptions
        currNamespace := ← getCurrNamespace
        openDecls := ← getOpenDecls
        env := ← getEnv
        expr := Expr.bvar 0 arbitrary
      }
    let mkExprWithCtx (e : Expr) : MetaM ExprText :=
      { tmpExprWithCtx with expr := e}.fmt
    withLCtx lctx mvarDecl.localInstances do
      let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Array (String × ExprText)) : MetaM (Array (String × ExprText)) :=
        if ids.isEmpty then
          pure fmt
        else
          match ids, type? with
          | [], _        => pure fmt
          | _, none      => pure fmt
          | _, some type => do
            pure $ fmt.push (Format.joinSep ids.reverse (format " ") |> toString, ← mkExprWithCtx type)
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Array (String × ExprText)) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Array (String × ExprText)) := do
        if hiddenProp.contains localDecl.fvarId then
          let fmt ← pushPending varNames prevType? fmt
          let type ← instantiateMVars localDecl.type
          let fmt  := fmt.push ("", ← mkExprWithCtx type)
          pure ([], none, fmt)
        else
          match localDecl with
          | LocalDecl.cdecl _ _ varName type _   =>
            let varName := varName.simpMacroScopes
            let type ← instantiateMVars type
            if prevType? == none || prevType? == some type then
              pure (varName :: varNames, some type, fmt)
            else do
              let fmt ← pushPending varNames prevType? fmt
              pure ([varName], some type, fmt)
          | LocalDecl.ldecl _ _ varName type val _ => do
            let varName := varName.simpMacroScopes
            let fmt ← pushPending varNames prevType? fmt
            let type ← instantiateMVars type
            let val  ← instantiateMVars val
            let typeFmt ← mkExprWithCtx type
            let fmt := fmt.push (format varName |> toString, typeFmt)
            pure ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, #[])) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if localDecl.isAuxDecl || hidden.contains localDecl.fvarId then
           pure (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let goalFmt ← mkExprWithCtx mvarDecl.type
      let userName? := match mvarDecl.userName with
        | Name.anonymous => none
        | name           => some <| toString name.eraseMacroScopes
      return { hyps := fmt, type := goalFmt, userName? }

open RequestM in
def getInteractiveGoals (p : Lsp.PlainGoalParams) : RequestM (RequestTask InteractiveGoals) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  -- NOTE: use `>=` since the cursor can be *after* the input
  withWaitFindSnap doc (fun s => s.endPos >= hoverPos)
    (notFoundX := return { goals := #[] }) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let rs@(_ :: _) := t.goalsAt? doc.meta.text hoverPos then
          let goals ← List.join <$> rs.mapM fun { ctxInfo := ci, tacticInfo := ti, useAfter := useAfter } =>
            let ci := if useAfter then { ci with mctx := ti.mctxAfter } else { ci with mctx := ti.mctxBefore }
            let goals := if useAfter then ti.goalsAfter else ti.goalsBefore
            ci.runMetaM {} <| goals.mapM (fun g => Meta.withPPInaccessibleNames (goalToInteractive g))
          return { goals := goals.toArray }

      return { goals := #[] }

open RequestM in
partial def getInteractiveTermGoal (p : Lsp.PlainTermGoalParams)
    : RequestM (RequestTask (Option InteractiveGoal)) := do
  let doc ← readDoc
  let text := doc.meta.text
  let hoverPos := text.lspPosToUtf8Pos p.position
  withWaitFindSnap doc (fun s => s.endPos > hoverPos)
    (notFoundX := pure none) fun snap => do
      for t in snap.cmdState.infoState.trees do
        if let some (ci, i@(Elab.Info.ofTermInfo ti)) := t.termGoalAt? hoverPos then
         let ty ← ci.runMetaM i.lctx do
           Meta.instantiateMVars <| ti.expectedType?.getD (← Meta.inferType ti.expr)
         -- for binders, hide the last hypothesis (the binder itself)
         let lctx' := if ti.isBinder then i.lctx.pop else i.lctx
         let goal ← ci.runMetaM lctx' do
           Meta.withPPInaccessibleNames <| goalToInteractive (← Meta.mkFreshExprMVar ty).mvarId!
         --let range := if let some r := i.range? then r.toLspRange text else ⟨p.position, p.position⟩
         return some goal
      return none

builtin_initialize
  registerRpcCallHandler `Lean.Widget.getInteractiveGoals    Lsp.PlainGoalParams     InteractiveGoals         getInteractiveGoals
  registerRpcCallHandler `Lean.Widget.getInteractiveTermGoal Lsp.PlainTermGoalParams (Option InteractiveGoal) getInteractiveTermGoal

end Lean.Widget
