/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Meta.InferType

namespace Lean.Meta

register_builtin_option pp.auxDecls : Bool := {
  defValue := false
  group    := "pp"
  descr    := "display auxiliary declarations used to compile recursive functions"
}

register_builtin_option pp.implementationDetailHyps : Bool := {
  defValue := false
  group    := "pp"
  descr    := "display implementation detail hypotheses in the local context"
}

register_builtin_option pp.inaccessibleNames : Bool := {
  defValue := true
  group    := "pp"
  descr    := "display inaccessible declarations in the local context"
}

register_builtin_option pp.showLetValues : Bool := {
  defValue := true
  group    := "pp"
  descr    := "display let-declaration values in the info view"
}

private def addLine (fmt : Format) : Format :=
  if fmt.isNil then fmt else fmt ++ Format.line

def getGoalPrefix (mvarDecl : MetavarDecl) : String :=
  if isLHSGoal? mvarDecl.type |>.isSome then
    -- use special prefix for `conv` goals
    "| "
  else
    "⊢ "

def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => return "unknown goal"
  | some mvarDecl =>
    let indent         := 2 -- Use option
    let showLetValues  := pp.showLetValues.get (← getOptions)
    let ppAuxDecls     := pp.auxDecls.get (← getOptions)
    let ppImplDetailHyps := pp.implementationDetailHyps.get (← getOptions)
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
      -- The following two `let rec`s are being used to control the generated code size.
      -- Then should be remove after we rewrite the compiler in Lean
      let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format := do
        if ids.isEmpty then
          return fmt
        else
          let fmt := addLine fmt
          match type? with
          | none      => return fmt
          | some type =>
            let typeFmt ← ppExpr type
            return fmt ++ (Format.joinSep ids.reverse (format " ") ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
      let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
        match localDecl with
        | .cdecl _ _ varName type _ _ =>
          let varName := varName.simpMacroScopes
          let type ← instantiateMVars type
          if prevType? == none || prevType? == some type then
            return (varName :: varNames, some type, fmt)
          else do
            let fmt ← pushPending varNames prevType? fmt
            return ([varName], some type, fmt)
        | .ldecl _ _ varName type val _ _ => do
          let varName := varName.simpMacroScopes
          let fmt ← pushPending varNames prevType? fmt
          let fmt  := addLine fmt
          let type ← instantiateMVars type
          let typeFmt ← ppExpr type
          let mut fmtElem  := format varName ++ " : " ++ typeFmt
          if showLetValues then
            let val ← instantiateMVars val
            let valFmt ← ppExpr val
            fmtElem := fmtElem ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)
          let fmt := fmt ++ fmtElem.group
          return ([], none, fmt)
      let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
         if !ppAuxDecls && localDecl.isAuxDecl || !ppImplDetailHyps && localDecl.isImplementationDetail then
           return (varNames, prevType?, fmt)
         else
           ppVars varNames prevType? fmt localDecl
      let fmt ← pushPending varNames type? fmt
      let fmt := addLine fmt
      let typeFmt ← ppExpr (← instantiateMVars mvarDecl.type)
      let fmt := fmt ++ getGoalPrefix mvarDecl ++ Format.nest indent typeFmt
      match mvarDecl.userName with
      | Name.anonymous => return fmt
      | name           => return "case " ++ format name.eraseMacroScopes ++ Format.line ++ fmt

end Lean.Meta
