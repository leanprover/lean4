/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Elab.AuxDef
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Elab.Command.aux_def]
public def fmtAuxDef : Fmt := fun
  | `(Lean.Elab.Command.aux_def|
      $[$docComment?:docComment]? $[$attributes?:attributes]? $visibility:visibility
      aux_def%$auxDefTk $suggestions:ident* :%$colonTk $type:term :=%$colonEqTk $body:term) => do
    let auxDefTk ← fmt auxDefTk
    let suggestions ← fmtArray suggestions
    let colonTk ← fmt colonTk
    let type ← fmt type
    let colonEqTk ← fmt colonEqTk
    let body ← fmt body
    let signature := Layouts.globalSignature (#[auxDefTk] ++ suggestions) #[] colonTk type
    let decl := Layouts.assignmentDeclaration signature colonEqTk body
    fmtDeclWithModifiers docComment? attributes? #[visibility] decl
  | _ => throw .partialFormatter
