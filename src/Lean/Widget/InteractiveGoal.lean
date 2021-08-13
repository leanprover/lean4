/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki
-/
import Lean.Widget.InteractiveCode

/-! RPC procedures for retrieving tactic and term goals with embedded `CodeWithInfos`. -/
-- TODO(WN): this module is mostly a slightly adapted copy of the corresponding `plainGoal/plainTemGoal` handlers
-- unify them

namespace Lean.Widget
open Server

structure InteractiveGoal where
  hyps      : Array (String × CodeWithInfos)
  type      : CodeWithInfos
  userName? : Option String
  deriving Inhabited, RpcEncoding

namespace InteractiveGoal

def pretty (g : InteractiveGoal) : String :=
  let ret := match g.userName? with
    | some userName => s!"case {userName}\n"
    | none          => ""
  let hyps := g.hyps.map fun (name, tt) => s!"{name} : {tt.stripTags}"
  let ret := ret ++ "\n".intercalate hyps.toList
  ret ++ s!"⊢ {g.type.stripTags}"

end InteractiveGoal

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
    let mkExprWithCtx (e : Expr) : MetaM CodeWithInfos :=
      exprToInteractive e
    withLCtx lctx mvarDecl.localInstances do
      let (hidden, hiddenProp) ← ToHide.collect mvarDecl.type
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Array (String × CodeWithInfos)) : MetaM (Array (String × CodeWithInfos)) :=
        if ids.isEmpty then
          pure fmt
        else
          match ids, type? with
          | [], _        => pure fmt
          | _, none      => pure fmt
          | _, some type => do
            pure $ fmt.push (Format.joinSep ids.reverse (format " ") |> toString, ← mkExprWithCtx type)
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Array (String × CodeWithInfos)) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Array (String × CodeWithInfos)) := do
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

end Lean.Widget
