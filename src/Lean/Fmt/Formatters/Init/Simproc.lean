/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Init.Simproc
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

public def fmtSimprocLike
    (docComment? : Option (TSyntax ``Parser.Command.docComment)) (mods : Array (Option Syntax))
    (simprocTk : Syntax) (phase? : Option Syntax) (lbTk? : Option Syntax)
    (ids? : Option (Syntax.TSepArray `ident ",")) (rbTk? : Option Syntax) (declId : TSyntax `ident)
    (lparenTk : Syntax) (trigger : TSyntax `term) (rparenTk : Syntax) (colonEqTk : Syntax)
    (body : TSyntax `term)
    : FmtM TaggedDoc := do
  let simprocTk ← fmt simprocTk
  let phase? ← fmt? phase?
  let lbTk? ← fmt? lbTk?
  let ids ← fmtTSepArray (ids?.getD ⟨#[]⟩)
  let rbTk? ← fmt? rbTk?
  let declId ← fmt declId
  let lparenTk ← fmt lparenTk
  let trigger ← fmt trigger
  let rparenTk ← fmt rparenTk
  let colonEqTk ← fmt colonEqTk
  let body ← fmt body
  let keyword := Layouts.spacedAtomic #[simprocTk, phase?]
  let ids := Layouts.collection lbTk? ids rbTk?
  let trigger := Layouts.parens lparenTk trigger rparenTk
  let declaration := Layouts.pseudoApplication #[declId, trigger]
  let signature := Layouts.blocks #[keyword, ids, declaration]
  let decl := Layouts.assignmentDeclaration signature colonEqTk body
  fmtDeclWithModifiers docComment? none mods decl

public def fmtSimprocPatternLike
    (simprocPatternTk : Syntax) (pattern : TSyntax `term) (arrowTk : Syntax)
    (declId : TSyntax `ident)
    : FmtM TaggedDoc := do
  let simprocPatternTk ← fmt simprocPatternTk
  let pattern ← fmt pattern
  let arrowTk ← fmt arrowTk
  let declId ← fmt declId
  let assignment := Layouts.assignmentDeclaration pattern arrowTk declId
  return Layouts.pseudoApplication #[simprocPatternTk, assignment]

public def fmtSimprocAttrLike (simprocTk : Syntax) (phase? : Option Syntax) : FmtM TaggedDoc := do
  let simprocTk ← fmt simprocTk
  let phase? ← fmt? phase?
  return Layouts.spacedAtomic #[simprocTk, phase?]

@[builtin_fmt Lean.Parser.«command__Simproc__[_]_(_):=_»]
public def fmtSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind simproc%$simprocTk $[$phase?]? $[ [%$lbTk? $ids?:ident,* ]%$rbTk? ]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] simprocTk phase? lbTk? ids? rbTk? declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command__Dsimproc__[_]_(_):=_»]
public def fmtDSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind dsimproc%$dsimprocTk $[$phase?]? $[ [%$lbTk? $ids?:ident,* ]%$rbTk? ]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] dsimprocTk phase? lbTk? ids? rbTk? declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Simproc_decl_(_):=_»]
public def fmtSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      simproc_decl%$simprocDeclTk $declId:ident (%$lparenTk $trigger:term )%$rparenTk
        :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] simprocDeclTk none none none none declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Dsimproc_decl_(_):=_»]
public def fmtDSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      dsimproc_decl%$dsimprocDeclTk $declId:ident (%$lparenTk $trigger:term )%$rparenTk
        :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] dsimprocDeclTk none none none none declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command__Builtin_simproc__[_]_(_):=_»]
public def fmtBuiltinSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind builtin_simproc%$builtinSimprocTk $[$phase?]?
        $[ [%$lbTk? $ids?:ident,* ]%$rbTk? ]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] builtinSimprocTk phase? lbTk? ids? rbTk? declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command__Builtin_dsimproc__[_]_(_):=_»]
public def fmtBuiltinDSimproc : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      $attrKind:attrKind builtin_dsimproc%$builtinDSimprocTk $[$phase?]?
        $[ [%$lbTk? $ids?:ident,* ]%$rbTk? ]?
        $declId:ident (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[attrKind] builtinDSimprocTk phase? lbTk? ids? rbTk? declId lparenTk
      trigger rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Builtin_simproc_decl_(_):=_»]
public def fmtBuiltinSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      builtin_simproc_decl%$builtinSimprocDeclTk $declId:ident
        (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] builtinSimprocDeclTk none none none none declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.«command_Builtin_dsimproc_decl_(_):=_»]
public def fmtBuiltinDSimprocDecl : Fmt := fun
  | `(command|
      $[$docComment?:docComment]?
      builtin_dsimproc_decl%$builtinDSimprocDeclTk $declId:ident
        (%$lparenTk $trigger:term )%$rparenTk :=%$colonEqTk $body:term) =>
    fmtSimprocLike docComment? #[] builtinDSimprocDeclTk none none none none declId lparenTk trigger
      rparenTk colonEqTk body
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.simprocPattern]
public def fmtSimprocPattern : Fmt := fun
  | `(Parser.simprocPattern|
      simproc_pattern%%$simprocPatternTk $pattern:term =>%$arrowTk $declId:ident) =>
    fmtSimprocPatternLike simprocPatternTk pattern arrowTk declId
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.simprocPatternBuiltin]
public def fmtBuiltinSimprocPattern : Fmt := fun
  | `(Parser.simprocPatternBuiltin|
      builtin_simproc_pattern%%$simprocPatternTk $pattern:term =>%$arrowTk $declId:ident) =>
    fmtSimprocPatternLike simprocPatternTk pattern arrowTk declId
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.simprocAttr]
public def fmtSimprocAttr : Fmt := fun
  | `(Parser.Attr.simprocAttr| simproc%$simprocTk $[$phase?]?) =>
    fmtSimprocAttrLike simprocTk phase?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.sevalprocAttr]
public def fmtSevalprocAttr : Fmt := fun
  | `(Parser.Attr.sevalprocAttr| sevalproc%$sevalprocTk $[$phase?]?) =>
    fmtSimprocAttrLike sevalprocTk phase?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.simprocBuiltinAttr]
public def fmtBuiltinSimprocAttr : Fmt := fun
  | `(Parser.Attr.simprocBuiltinAttr| builtin_simproc%$builtinSimprocTk $[$phase?]?) =>
    fmtSimprocAttrLike builtinSimprocTk phase?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Parser.Attr.sevalprocBuiltinAttr]
public def fmtBuiltinSevalprocAttr : Fmt := fun
  | `(Parser.Attr.sevalprocBuiltinAttr| builtin_sevalproc%$builtinSevalprocTk $[$phase?]?) =>
    fmtSimprocAttrLike builtinSevalprocTk phase?
  | _ =>
    throw .partialFormatter
