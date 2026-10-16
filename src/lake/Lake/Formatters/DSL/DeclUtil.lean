/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lake.DSL.DeclUtil
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt Lake.DSL

namespace Lake.Formatters

@[builtin_fmt Lake.DSL.identOrStr]
public def fmtIdentOrStr : Fmt := fun
  | `(identOrStr| $id:ident) => fmt id
  | `(identOrStr| $name:str) => fmt name
  | _ => throw .partialFormatter

@[builtin_fmt Lake.DSL.declField]
public def fmtDeclField : Fmt := fun
  | `(declField| $id:ident :=%$colonEqTk $val:term) => do
    let id ← fmt id
    let colonEqTk ← fmt colonEqTk
    let val ← fmt val
    return Layouts.assignmentDeclaration id colonEqTk val
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.bracketedSimpleBinder]
public def fmtBracketedSimpleBinder : Fmt := fun
  | `(bracketedSimpleBinder| (%$lbTk $id:ident $[:%$typeAscriptionTk? $type?:term]? )%$rbTk) =>
    fmtBinder #[lbTk] #[id] #[] typeAscriptionTk? type? none #[rbTk] (kind := .global)
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.DSL.simpleBinder]
public def fmtSimpleBinder : Fmt := fun
  | `(simpleBinder| $id:ident) => fmt id
  | `(simpleBinder| $binder:bracketedSimpleBinder) => fmt binder
  | _ => throw .partialFormatter

/--
Formats a declaration with the `signature` document and the declarative configuration `config`,
i.e. either nothing, a `{ ... }` configuration or a `where ...` configuration.
-/
public def fmtWithOptConfig (signature : TaggedDoc) (config : OptConfig) : FmtM TaggedDoc := do
  match config with
  | `(optConfig| ) =>
    return signature
  | `(optConfig| $structVal:structVal $[$whereDecls?:whereDecls]?) =>
    let `(structVal| {%$lbTk $fields:declField;* }%$rbTk) := structVal
      | throw .partialFormatter
    let lbTk ← fmt lbTk
    let fields ← fmtTSepArray fields
    let rbTk ← fmt rbTk
    let mainDeclTrailingDoc ← fmtTrailingWithRetainedNewlinesAndComments structVal
    let whereDecls? ← fmt? whereDecls?
    let fields := withPosition <| Layouts.sepLines fields (includeSeps := false)
    let structVal := Layouts.bracketed lbTk fields rbTk <| .sparse nl
    let mainDecl := Layouts.assignmentDeclaration signature empty structVal
    return Layouts.retainedWhitespace #[
      mainDecl,
      mainDeclTrailingDoc,
      whereDecls?
    ]
  | `(optConfig| where%$whereTk $fields:declField;* $[$whereDecls?:whereDecls]?) =>
    let whereTkDoc ← fmt whereTk
    let fieldsDoc ← fmtTSepArray fields
    let mainDeclTrailingDoc ←
      fmtTrailingWithRetainedNewlinesAndComments <| mkNullNode <| #[whereTk] ++ fields
    let whereDecls? ← fmt? whereDecls?
    let fieldsDoc := withPosition <| Layouts.sepLines fieldsDoc (includeSeps := false)
    let mainDecl := Layouts.whereDeclaration signature whereTkDoc fieldsDoc
    return Layouts.retainedWhitespace #[
      mainDecl,
      mainDeclTrailingDoc,
      whereDecls?
    ]
  | _ =>
    throw .partialFormatter
