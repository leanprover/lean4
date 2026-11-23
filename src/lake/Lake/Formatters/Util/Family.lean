/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lake.Util.Family
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt

namespace Lake.Formatters

@[builtin_fmt Lake.familyDef]
public def fmtFamilyDef : Fmt := fun
  | `(familyDef|
      $[$docComment?:docComment]? family_def%$familyDefTk $id:ident :%$typeAscriptionTk
        $fam:ident $idx:term :=%$colonEqTk $val:term) => do
    let familyDefTk ← fmt familyDefTk
    let id ← fmt id
    let typeAscriptionTk ← fmt typeAscriptionTk
    let family ← fmtAppLike #[fam, idx]
    let colonEqTk ← fmt colonEqTk
    let val ← fmt val
    let signature := Layouts.globalSignature #[familyDefTk, id] #[] typeAscriptionTk family
    let decl := Layouts.assignmentDeclaration signature colonEqTk val
    fmtDeclWithModifiers docComment? none #[] decl
  | _ => throw .partialFormatter
