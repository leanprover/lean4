/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
public import Lean.Fmt.Formatters.Lean.Parser.Term
meta import Lean.Elab.ConfigEval.Commands
meta import Lean.Parser.Command
import Lean.Fmt.FmtM.CommonFormatters
import Init.Data

namespace Lean.Fmt

/-- Formats the `<visibility> <attrKind> <keyword> <type>` instance-ensuring commands. -/
public def fmtEnsureEvalInstance
    (visibility? : Option Syntax) (attrKind : TSyntax ``Parser.Term.attrKind) (keywordTk : Syntax)
    (type : TSyntax `term)
    : FmtM TaggedDoc := do
  let keywordTk ← fmt keywordTk
  let type ← fmt type
  let decl := Layouts.pseudoApplication #[keywordTk, type]
  fmtDeclWithModifiers none none #[visibility?, attrKind] decl

@[builtin_fmt Lean.Elab.ConfigEval.ensureEvalTermInstance]
public def fmtEnsureEvalTermInstance : Fmt := fun
  | `(Lean.Elab.ConfigEval.ensureEvalTermInstance|
      $[$visibility?:visibility]? $attrKind:attrKind ensure_eval_term_instance%$keywordTk $type:term) =>
    fmtEnsureEvalInstance visibility? attrKind keywordTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.ensureEvalExprInstance]
public def fmtEnsureEvalExprInstance : Fmt := fun
  | `(Lean.Elab.ConfigEval.ensureEvalExprInstance|
      $[$visibility?:visibility]? $attrKind:attrKind ensure_eval_expr_instance%$keywordTk $type:term) =>
    fmtEnsureEvalInstance visibility? attrKind keywordTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.ensureEvalTermExprInstances]
public def fmtEnsureEvalTermExprInstances : Fmt := fun
  | `(Lean.Elab.ConfigEval.ensureEvalTermExprInstances|
      $[$visibility?:visibility]? $attrKind:attrKind
      ensure_eval_term_expr_instances%$keywordTk $type:term) =>
    fmtEnsureEvalInstance visibility? attrKind keywordTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.deriveEvalExprUsingMeta]
public def fmtDeriveEvalExprUsingMeta : Fmt := fun
  | `(Lean.Elab.ConfigEval.deriveEvalExprUsingMeta|
      $[$visibility?:visibility]? $attrKind:attrKind
      derive_eval_expr_instance_using_meta_eval%$keywordTk $type:term) =>
    fmtEnsureEvalInstance visibility? attrKind keywordTk type
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.configEntryOmit]
public def fmtConfigEntryOmit : Fmt := fun
  | `(Lean.Elab.ConfigEval.configEntryOmit| omit%$omitTk $fields:ident,*) => do
    let omitTk ← fmt omitTk
    let fields ← fmtTSepArray fields
    return Layouts.keywordPrefixedSepFill omitTk fields .nonSticky
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.configEntryHandlerKeyPrefix]
public def fmtConfigEntryHandlerKeyPrefix : Fmt := fun
  | `(Lean.Elab.ConfigEval.configEntryHandlerKeyPrefix| $key:ident$[.%$dotTk?*%$starTk?]?) => do
    let key ← fmt key
    let dotTk? ← fmt? dotTk?
    let starTk? ← fmt? starTk?
    return Layouts.atomic #[key, dotTk?, starTk?]
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.configEntryHandlerKey]
public def fmtConfigEntryHandlerKey : Fmt := fun
  | `(Lean.Elab.ConfigEval.configEntryHandlerKey| $key:configEntryHandlerKeyPrefix) => fmt key
  | `(Lean.Elab.ConfigEval.configEntryHandlerKey| $key:configEntryHandlerKeyWildcard) => fmt key
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.configEntryHandler]
public def fmtConfigEntryHandler : Fmt := fun
  | `(Lean.Elab.ConfigEval.configEntryHandler|
      option%$optionTk $key:configEntryHandlerKey :=%$colonEqTk $handler:term) => do
    let optionTk ← fmt optionTk
    let key ← fmt key
    let colonEqTk ← fmt colonEqTk
    let handler ← fmt handler
    let signature := Layouts.pseudoApplication #[optionTk, key]
    return Layouts.assignmentDeclaration signature colonEqTk handler
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.configEntry]
public def fmtConfigEntry : Fmt := fun
  | `(Lean.Elab.ConfigEval.configEntry| $entry:configEntryOmit) => fmt entry
  | `(Lean.Elab.ConfigEval.configEntry| $entry:configEntryHandler) => fmt entry
  | _ => throw .partialFormatter

/-- Attaches the optional `where` clause of a configuration command to `signature`. -/
public def fmtWithConfigEntries
    (signature : TaggedDoc) (configEntries? : Option (TSyntax ``Lean.Elab.ConfigEval.configEntries))
    : FmtM TaggedDoc := do
  let some configEntries := configEntries?
    | return signature
  let `(Lean.Elab.ConfigEval.configEntries| where%$whereTk $entries:configEntry;*) := configEntries
    | throw .partialFormatter
  let whereTk ← fmt whereTk
  let entries ← fmtSeq entries none
  return Layouts.whereDeclaration signature whereTk entries

@[builtin_fmt Lean.Elab.ConfigEval.defEvalConfigItemCmd]
public def fmtDefEvalConfigItemCmd : Fmt := fun
  | `(Lean.Elab.ConfigEval.defEvalConfigItemCmd|
      $[$docComment?:docComment]? $[$visibility?:visibility]? $attrKind:attrKind
      def_eval_config_item%$defTk $itemId:ident $[$binders:bracketedBinder]*
      for%$forTk $structId:ident $[$configEntries?:configEntries]?) => do
    let defTk ← fmt defTk
    let itemId ← fmt itemId
    let binders ← fmtBinders (convertBracketedBinders binders)
    let forTk ← fmt forTk
    let structId ← fmt structId
    let signature := Layouts.globalSignature #[defTk, itemId] binders empty empty
    let «for» := Layouts.keywordPrefixedTerm forTk structId .nonSticky
    let signature :=
      Layouts.blocks #[
        { block := signature, hardNestedIfFirst := false },
        { block := «for» }
      ]
    let decl ← fmtWithConfigEntries signature configEntries?
    fmtDeclWithModifiers docComment? none #[visibility?, attrKind] decl
  | _ =>
    throw .partialFormatter

/-- Formats the `declare_*_config_elab` commands, which only differ in their keyword. -/
public def fmtDeclareConfig
    (docComment? : Option (TSyntax ``Parser.Command.docComment)) (visibility? : Option Syntax)
    (declTk : Syntax) (elabId structId : TSyntax `ident)
    (binders : TSyntaxArray [``Parser.Term.bracketedBinder])
    (configEntries? : Option (TSyntax ``Lean.Elab.ConfigEval.configEntries))
    : FmtM TaggedDoc := do
  let declTk ← fmt declTk
  let elabId ← fmt elabId
  let structId ← fmt structId
  let binders ← fmtBinders (convertBracketedBinders binders)
  let signature := Layouts.globalSignature #[declTk, elabId, structId] binders empty empty
  let decl ← fmtWithConfigEntries signature configEntries?
  fmtDeclWithModifiers docComment? none #[visibility?] decl

@[builtin_fmt Lean.Elab.ConfigEval.declareCoreConfigElab]
public def fmtDeclareCoreConfigElab : Fmt := fun
  | `(Lean.Elab.ConfigEval.declareCoreConfigElab|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      declare_core_config_elab%$declTk $elabId:ident $structId:ident
      $[$binders:bracketedBinder]* $[$configEntries?:configEntries]?) =>
    fmtDeclareConfig docComment? visibility? declTk elabId structId binders configEntries?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.declareTermConfigElab]
public def fmtDeclareTermConfigElab : Fmt := fun
  | `(Lean.Elab.ConfigEval.declareTermConfigElab|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      declare_term_config_elab%$declTk $elabId:ident $structId:ident
      $[$binders:bracketedBinder]* $[$configEntries?:configEntries]?) =>
    fmtDeclareConfig docComment? visibility? declTk elabId structId binders configEntries?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.declareTacticConfig]
public def fmtDeclareTacticConfig : Fmt := fun
  | `(Lean.Elab.ConfigEval.declareTacticConfig|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      declare_config_elab%$declTk $elabId:ident $structId:ident
      $[$binders:bracketedBinder]* $[$configEntries?:configEntries]?) =>
    fmtDeclareConfig docComment? visibility? declTk elabId structId binders configEntries?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Elab.ConfigEval.declareCommandConfig]
public def fmtDeclareCommandConfig : Fmt := fun
  | `(Lean.Elab.ConfigEval.declareCommandConfig|
      $[$docComment?:docComment]? $[$visibility?:visibility]?
      declare_command_config_elab%$declTk $elabId:ident $structId:ident
      $[$binders:bracketedBinder]* $[$configEntries?:configEntries]?) =>
    fmtDeclareConfig docComment? visibility? declTk elabId structId binders configEntries?
  | _ =>
    throw .partialFormatter
