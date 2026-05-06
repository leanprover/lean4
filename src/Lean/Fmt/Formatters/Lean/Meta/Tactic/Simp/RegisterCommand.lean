/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

-- `macro (name := _root_.…)` keeps the `_root_` component in the node kind while dropping it from
-- the parser declaration, so the kind is not the name the quotation below refers to.
@[builtin_fmt Lean.Meta.Simp._root_.Lean.Parser.Command.registerSimpAttr]
public def fmtRegisterSimpAttr : Fmt := fun
  | `(Parser.Command.registerSimpAttr|
      $[$docComment?:docComment]? register_simp_attr%$registerTk $id:ident) => do
    let registerTk ← fmt registerTk
    let id ← fmt id
    let decl := Layouts.pseudoApplication #[registerTk, id]
    fmtDeclWithModifiers docComment? none #[] decl
  | _ =>
    throw .partialFormatter
