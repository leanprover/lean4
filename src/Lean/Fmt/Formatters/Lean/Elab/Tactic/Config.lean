/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Elab.Tactic.Config
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

/--
Formats the deprecated `declare_*_config_elab_legacy` commands, which only differ in their keyword.
-/
public def fmtDeclareConfigElabLegacy
    (docComment? : Option (TSyntax ``Parser.Command.docComment)) (declTk : Syntax)
    (elabId typeId : TSyntax `ident)
    : FmtM TaggedDoc := do
  let declTk ← fmt declTk
  let elabId ← fmt elabId
  let typeId ← fmt typeId
  let decl := Layouts.pseudoApplication #[declTk, elabId, typeId]
  fmtDeclWithModifiers docComment? none #[] decl

@[builtin_fmt Lean.Elab.Tactic.configElab]
public def fmtConfigElabLegacy : Fmt := fun
  | `(Lean.Elab.Tactic.configElab|
      $[$docComment?:docComment]? declare_config_elab_legacy%$declTk $elabId:ident $typeId:ident) =>
    fmtDeclareConfigElabLegacy docComment? declTk elabId typeId
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.Tactic.commandConfigElab]
public def fmtCommandConfigElabLegacy : Fmt := fun
  | `(Lean.Elab.Tactic.commandConfigElab|
      $[$docComment?:docComment]?
      declare_command_config_elab_legacy%$declTk $elabId:ident $typeId:ident) =>
    fmtDeclareConfigElabLegacy docComment? declTk elabId typeId
  | _ =>
    throw .partialFormatter
