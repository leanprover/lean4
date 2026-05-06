/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lake.Util.OpaqueType
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

open Lean Lean.Fmt

namespace Lake.Formatters

@[builtin_fmt Lake.nonemptyTypeCmd]
public def fmtNonemptyTypeCmd : Fmt := fun
  | `(nonemptyTypeCmd|
      $[$docComment?:docComment]? $[$visibility?:visibility]? nonempty_type%$nonemptyTypeTk
        $id:ident $[$binders]*) => do
    -- `Lake.binder` is `binderIdent <|> bracketedBinder`, i.e. exactly the declaration binders.
    let binders := binders.map fun binder => ⟨binder.raw⟩
    let signature ← fmtDeclarationSignature #[nonemptyTypeTk] none id binders none none
    fmtDeclWithModifiers docComment? none #[visibility?] signature
  | _ => throw .partialFormatter

@[builtin_fmt Lake.hydrateOpaqueTypeCmd]
public def fmtHydrateOpaqueTypeCmd : Fmt := fun
  | `(hydrateOpaqueTypeCmd|
      $[$visibility?:visibility]? hydrate_opaque_type%$hydrateOpaqueTypeTk $opaqueTy:ident
        $ty:ident $args:ident*) => do
    let hydrateOpaqueTypeTk ← fmt hydrateOpaqueTypeTk
    let opaqueTy ← fmt opaqueTy
    let ty ← fmt ty
    let args ← fmtArray args
    let decl := Layouts.pseudoApplication <| #[hydrateOpaqueTypeTk, opaqueTy, ty] ++ args
    fmtDeclWithModifiers none none #[visibility?] decl
  | _ => throw .partialFormatter
