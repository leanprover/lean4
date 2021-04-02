/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Environment
import Lean.Data.Lsp.LanguageFeatures
import Lean.Server.InfoUtils

namespace Lean.Server.Completion
open Lsp

builtin_initialize completionBlackListExt : TagDeclarationExtension ← mkTagDeclarationExtension `blackListCompletion

@[export lean_completion_add_to_black_list]
def addToBlackList (env : Environment) (declName : Name) : Environment :=
  completionBlackListExt.tag env declName

private def isBlackListed (env : Environment) (declName : Name) : Bool :=
  completionBlackListExt.isTagged env declName

private def isBlackListedForCompletion (declName : Name) : MetaM Bool := do
  let env ← getEnv
  return isAuxRecursor env declName || isNoConfusion env declName || (← isRec declName)

open Elab in open Meta in
partial def find? (fileMap : FileMap) (hoverPos : String.Pos) (infoTree : InfoTree) : IO (Option CompletionList) := do
  let ⟨hoverLine, _⟩ := fileMap.toPosition hoverPos
  if let some (ctx, Info.ofDotCompletionInfo info) := infoTree.foldInfo (init := none) (choose fileMap hoverLine) then
    info.runMetaM ctx do
      dbg_trace ">> {info.stx}, {info.expr}"
      let type ← instantiateMVars (← inferType info.expr)
      match type.getAppFn with
      | Expr.const name .. =>
        let candidates := (← getEnv).constants.fold (init := #[]) fun candidates declName declInfo =>
          if !declName.isInternal && declName.getPrefix == name then candidates.push declInfo else candidates
        let items : Array CompletionItem ← candidates.filterMapM fun cinfo => do
          if (← isBlackListedForCompletion cinfo.name) then
            return none
          else
            let detail ← Meta.ppExpr cinfo.type
            return some { label := cinfo.name.getString!, detail? := some (toString detail), documentation? := none }
        return some { items := items, isIncomplete := true }
      | _ => return none
  else
    return none
where
  choose (fileMap : FileMap) (hoverLine : Nat) (ctx : ContextInfo) (info : Info) (best? : Option (ContextInfo × Info)) : Option (ContextInfo × Info) :=
    if !info.isDotCompletion then best?
    else if let some d := info.occursBefore? hoverPos then
      let pos := info.tailPos?.get!
      let ⟨line, _⟩ := fileMap.toPosition pos
      if line != hoverLine then best?
      else match best? with
        | none => return (ctx, info)
        | some (_, best) =>
          let dBest := best.occursBefore? hoverPos |>.get!
          if d < dBest || (d == dBest && info.isSmaller best) then
            return (ctx, info)
          else
            best?
    else
      best?

end Lean.Server.Completion