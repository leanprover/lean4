/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Linter.Sets
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

@[builtin_fmt Lean.Linter.«command_Register_linter_set_:=_»]
public def fmtRegisterLinterSet : Fmt := fun
  | `(Lean.Linter.«command_Register_linter_set_:=_»|
      $[$docComment?:docComment]? register_linter_set%$registerTk $name:ident :=%$colonEqTk
        $decls:ident*) => do
    let registerTk ← fmt registerTk
    let name ← fmt name
    let colonEqTk ← fmt colonEqTk
    let decls ← fmtArray decls
    let decls := Layouts.fill decls
    let signature := Layouts.pseudoApplication #[registerTk, name]
    let decl := Layouts.assignmentDeclaration signature colonEqTk decls
    fmtDeclWithModifiers docComment? none #[] decl
  | _ => throw .partialFormatter
