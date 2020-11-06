/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
import Lean.Util.PPExt

namespace Lean

def ppAuxDeclsDefault := false
builtin_initialize
  registerOption `pp.auxDecls { defValue := ppAuxDeclsDefault, group := "pp", descr := "display auxiliary declarations used to compile recursive functions" }
def getAuxDeclsOption (o : Options) : Bool :=
  o.get `pp.auxDecls ppAuxDeclsDefault

def ppGoal (ppCtx : PPContext) (mvarId : MVarId) : IO Format :=
  let env  := ppCtx.env
  let mctx := ppCtx.mctx
  let opts := ppCtx.opts
  match mctx.findDecl? mvarId with
  | none          => pure "unknown goal"
  | some mvarDecl => do
    let indent       := 2 -- Use option
    let ppAuxDecls   := getAuxDeclsOption opts
    let lctx         := mvarDecl.lctx
    let lctx         := lctx.sanitizeNames.run' { options := opts }
    let ppCtx        := { ppCtx with lctx := lctx }
    let pp (e : Expr) : IO Format := ppExpr ppCtx e
    let instMVars (e : Expr) : Expr := mctx.instantiateMVars e $.1
    let addLine (fmt : Format) : Format := if fmt.isNil then fmt else fmt ++ Format.line
    let pushPending (ids : List Name) (type? : Option Expr) (fmt : Format) : IO Format :=
      if ids.isEmpty then
        pure fmt
      else
        let fmt := addLine fmt
        match ids, type? with
        | [], _        => pure fmt
        | _, none      => pure fmt
        | _, some type => do
          let typeFmt ← pp type
          pure $ fmt ++ (Format.joinSep ids.reverse " " ++ " :" ++ Format.nest indent (Format.line ++ typeFmt)).group
    let (varNames, type?, fmt) ← lctx.foldlM
      (fun (acc : List Name × Option Expr × Format) (localDecl : LocalDecl) =>
         if !ppAuxDecls && localDecl.isAuxDecl then pure acc else
         let (varNames, prevType?, fmt) := acc
         match localDecl with
         | LocalDecl.cdecl _ _ varName type _   =>
           let varName := varName.simpMacroScopes
           let type := instMVars type
           if prevType? == none || prevType? == some type then
             pure (varName :: varNames, some type, fmt)
           else do
             let fmt ← pushPending varNames prevType? fmt
             pure ([varName], some type, fmt)
         | LocalDecl.ldecl _ _ varName type val _ => do
           let varName := varName.simpMacroScopes
           let fmt ← pushPending varNames prevType? fmt
           let fmt  := addLine fmt
           let type := instMVars type
           let val  := instMVars val
           let typeFmt ← pp type
           let valFmt ← pp val
           let fmt  := fmt ++ (format varName ++ " : " ++ typeFmt ++ " :=" ++ Format.nest indent (Format.line ++ valFmt)).group
           pure ([], none, fmt))
      ([], none, Format.nil)
    let fmt ← pushPending varNames type? fmt
    let fmt := addLine fmt
    let typeFmt ← pp mvarDecl.type
    let fmt := fmt ++ "⊢" ++ " " ++ Format.nest indent typeFmt
    match mvarDecl.userName with
    | Name.anonymous => pure fmt
    | name           => pure $ "case " ++ format name.eraseMacroScopes ++ Format.line ++ fmt

end Lean
