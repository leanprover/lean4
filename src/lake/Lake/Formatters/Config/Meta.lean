/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lake.Config.Meta
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt

namespace Lake.Formatters

@[builtin_fmt Lake.configField]
public def fmtConfigField : Fmt := fun
  | `(configField|
      $declModifiers:declModifiers $[$id?:ident @%$atTk?]? $ids:ident,* $binders*
        :%$typeAscriptionTk $type:term $[:=%$colonEqTk? $defVal?:term]?) => do
    let id? ← fmt? id?
    let atTk? ← fmt? atTk?
    let ids ← fmtTSepArray ids
    let binders ← fmtBinders binders
    let typeAscriptionTk ← fmt typeAscriptionTk
    let type ← fmt type
    let colonEqTk? ← fmt? colonEqTk?
    let defVal? ← fmt? defVal?
    let ids := Layouts.sepFill ids
    let lhs := Layouts.infixOperator #[id?, atTk?, ids] .dense
    let field :=
      Layouts.binder #[] #[lhs] binders typeAscriptionTk type colonEqTk? defVal? #[]
        (kind := .global)
    fmtDeclWithDeclModifiers declModifiers field
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.configDecl]
public def fmtConfigDecl : Fmt := fun
  | `(configDecl|
      $declModifiers:declModifiers configuration%$configurationTk $declId:declId $binders*
        $[:%$typeAscriptionTk? $type?:term]? $[$extends?:extends]?
        $[where%$sepTk? $[$structCtor?:structCtor]? $configFields?*]?
      $optDeriving:optDeriving) => do
    let decl ←
      fmtStructureLike configurationTk declId binders typeAscriptionTk? type? extends? sepTk?
        structCtor?.join configFields? optDeriving
    fmtDeclWithDeclModifiers declModifiers decl
  | `(configDecl|
      $declModifiers:declModifiers configuration%$configurationTk $declId:declId $binders*
        $[:%$typeAscriptionTk? $type?:term]? $[$extends?:extends]?
        $[:=%$sepTk? $[$structCtor?:structCtor]? $configFields?*]?
      $optDeriving:optDeriving) => do
    let decl ←
      fmtStructureLike configurationTk declId binders typeAscriptionTk? type? extends? sepTk?
        structCtor?.join configFields? optDeriving
    fmtDeclWithDeclModifiers declModifiers decl
  | _ =>
    throw .partialFormatter
