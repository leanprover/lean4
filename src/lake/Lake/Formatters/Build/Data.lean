/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lake.Build.Data
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt

namespace Lake.Formatters

@[builtin_fmt Lake.dataTypeDecl]
public def fmtDataTypeDecl : Fmt := fun
  | `(dataTypeDecl|
      $[$docComment?:docComment]? data_type%$dataTypeTk $kind:ident :%$typeAscriptionTk
        $ty:term) => do
    let signature ← fmtDeclarationSignature #[dataTypeTk] none kind #[] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.builtinFacetCommand]
public def fmtBuiltinFacetCommand : Fmt := fun
  | `(builtinFacetCommand|
      $[$docComment?:docComment]? builtin_facet%$builtinFacetTk $[$id?:ident @%$atTk?]?
        $name:ident :%$typeAscriptionTk $ns:ident =>%$arrowTk $ty:term) => do
    let builtinFacetTk ← fmt builtinFacetTk
    let id? ← fmt? id?
    let atTk? ← fmt? atTk?
    let name ← fmt name
    let typeAscriptionTk ← fmt typeAscriptionTk
    let ns ← fmt ns
    let arrowTk ← fmt arrowTk
    let ty ← fmt ty
    let facet := Layouts.infixOperator #[id?, atTk?, name] .dense
    let signature := Layouts.globalSignature #[builtinFacetTk, facet] #[] typeAscriptionTk ns
    let decl := Layouts.assignmentDeclaration signature arrowTk ty
    fmtDeclWithModifiers docComment? none #[] decl
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.facetDataDecl]
public def fmtFacetDataDecl : Fmt := fun
  | `(facetDataDecl|
      $[$docComment?:docComment]? facet_data%$facetDataTk $kind:ident $name:ident
        :%$typeAscriptionTk $ty:term) => do
    let signature ← fmtDeclarationSignature #[facetDataTk] none kind #[name] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.customDataDecl]
public def fmtCustomDataDecl : Fmt := fun
  | `(customDataDecl|
      $[$docComment?:docComment]? custom_data%$customDataTk $pkg:ident $tgt:ident
        :%$typeAscriptionTk $ty:term) => do
    let signature ← fmtDeclarationSignature #[customDataTk] none pkg #[tgt] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.packageDataDecl]
public def fmtPackageDataDecl : Fmt := fun
  | `(packageDataDecl|
      $[$docComment?:docComment]? package_data%$packageDataTk $facet:ident :%$typeAscriptionTk
        $ty:term) => do
    let signature ← fmtDeclarationSignature #[packageDataTk] none facet #[] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.moduleDataDecl]
public def fmtModuleDataDecl : Fmt := fun
  | `(moduleDataDecl|
      $[$docComment?:docComment]? module_data%$moduleDataTk $facet:ident :%$typeAscriptionTk
        $ty:term) => do
    let signature ← fmtDeclarationSignature #[moduleDataTk] none facet #[] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lake.libraryDataDecl]
public def fmtLibraryDataDecl : Fmt := fun
  | `(libraryDataDecl|
      $[$docComment?:docComment]? library_data%$libraryDataTk $facet:ident :%$typeAscriptionTk
        $ty:term) => do
    let signature ← fmtDeclarationSignature #[libraryDataTk] none facet #[] typeAscriptionTk ty
    fmtDeclWithModifiers docComment? none #[] signature
  | _ =>
    throw .partialFormatter
