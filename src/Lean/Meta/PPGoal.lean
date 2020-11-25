/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Meta.Basic

namespace Lean.Meta

def ppAuxDeclsDefault := false
builtin_initialize
  registerOption `pp.auxDecls { defValue := ppAuxDeclsDefault, group := "pp", descr := "display auxiliary declarations used to compile recursive functions" }
def getAuxDeclsOption (o : Options) : Bool :=
  o.get `pp.auxDecls ppAuxDeclsDefault

def ppInaccessibleDefault := false
builtin_initialize
  registerOption `pp.inaccessible { defValue := ppInaccessibleDefault, group := "pp", descr := "display inaccessible declarations in the local context" }
def getInaccessibleOption (o : Options) : Bool :=
  o.get `pp.inaccessible ppInaccessibleDefault

def ppGoal (mvarId : MVarId) : MetaM Format := do
  match (← getMCtx).findDecl? mvarId with
  | none          => pure "unknown goal"
  | some mvarDecl => do
    let indent         := 2 -- Use option
    let ppAuxDecls     := getAuxDeclsOption (← getOptions)
    let ppInaccessible := getInaccessibleOption (← getOptions)
    let lctx           := mvarDecl.lctx
    let lctx           := lctx.sanitizeNames.run' { options := (← getOptions) }
    withLCtx lctx mvarDecl.localInstances do
    let addLine (fmt : Format) : Format := if fmt.isNil then fmt else fmt ++ Format.line
    -- The followint two `let rec`s are being used to control the generated code size.
    -- Then should be remove after we rewrite the compiler in Lean
    let rec pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : MetaM Format :=
      if ids.isEmpty then
        pure fmt
      else
        let fmt := addLine fmt
        match ids, type? with
        | [], _        => pure fmt
        | _, none      => pure fmt
        | _, some type => do
          let typeFmt ← ppExpr type
          pure $ fmt ++ (Format.joinSep ids.reverse " " ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
    let rec ppVars (varNames : List Name) (prevType? : Option Expr) (fmt : Format) (localDecl : LocalDecl) : MetaM (List Name × Option Expr × Format) := do
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
        let fmt  := addLine fmt
        let type ← instantiateMVars type
        let val  ← instantiateMVars val
        let typeFmt ← ppExpr type
        let valFmt ← ppExpr val
        let fmt  := fmt ++ (format varName ++ " : " ++ typeFmt ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)).group
        pure ([], none, fmt)
    let (varNames, type?, fmt) ← lctx.foldlM (init := ([], none, Format.nil)) fun (varNames, prevType?, fmt) (localDecl : LocalDecl) =>
       if !ppAuxDecls && localDecl.isAuxDecl then
         pure (varNames, prevType?, fmt)
       else
         ppVars varNames prevType? fmt localDecl
    let fmt ← pushPending varNames type? fmt
    let fmt := addLine fmt
    let typeFmt ← ppExpr mvarDecl.type
    let fmt := fmt ++ "⊢" ++ " " ++ Format.nest indent typeFmt
    match mvarDecl.userName with
    | Name.anonymous => pure fmt
    | name           => return "case " ++ format name.eraseMacroScopes ++ Format.line ++ fmt

end Lean.Meta
