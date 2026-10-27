/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Init.Simproc
meta import Init.CbvSimproc
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Parser.«command__Cbv_simproc____(_):=_»]
public def fmtCbvSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind cbv_simproc%$cbvSimprocTk $[$phase?]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] cbvSimprocTk phase? none none none declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Cbv_simproc_decl_(_):=_»]
public def fmtCbvSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      cbv_simproc_decl%$cbvSimprocDeclTk $declId:ident (%$lparenTk $trigger:term )%$rparenTk
        :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] cbvSimprocDeclTk none none none none declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command__Builtin_cbv_simproc____(_):=_»]
public def fmtBuiltinCbvSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind builtin_cbv_simproc%$builtinCbvSimprocTk $[$phase?]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] builtinCbvSimprocTk phase? none none none declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Builtin_cbv_simproc_decl_(_):=_»]
public def fmtBuiltinCbvSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      builtin_cbv_simproc_decl%$builtinCbvSimprocDeclTk $declId:ident
        (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] builtinCbvSimprocDeclTk none none none none declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.cbvSimprocPattern]
public def fmtCbvSimprocPattern : Fmt := fun
  | `(Parser.cbvSimprocPattern|
      cbv_simproc_pattern%%$cbvSimprocPatternTk $pattern:term =>%$arrowTk $declId:ident) =>
    fmtSimprocPatternLike cbvSimprocPatternTk pattern arrowTk declId
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.cbvSimprocPatternBuiltin]
public def fmtBuiltinCbvSimprocPattern : Fmt := fun
  | `(Parser.cbvSimprocPatternBuiltin|
      builtin_cbv_simproc_pattern%%$cbvSimprocPatternTk $pattern:term =>%$arrowTk $declId:ident) =>
    fmtSimprocPatternLike cbvSimprocPatternTk pattern arrowTk declId
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.cbvSimprocAttr]
public def fmtCbvSimprocAttr : Fmt := fun
  | `(Parser.Attr.cbvSimprocAttr| cbv_simproc%$cbvSimprocTk $[$phase?]?) =>
    fmtSimprocAttrLike cbvSimprocTk phase?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.cbvSimprocBuiltinAttr]
public def fmtBuiltinCbvSimprocAttr : Fmt := fun
  | `(Parser.Attr.cbvSimprocBuiltinAttr| builtin_cbv_simproc%$builtinCbvSimprocTk $[$phase?]?) =>
    fmtSimprocAttrLike builtinCbvSimprocTk phase?
  | _ =>
    throw .partialFormatter
