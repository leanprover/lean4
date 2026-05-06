/-
Copyright (c) 2026 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.FmtM.Basic
meta import Lean.Widget.Commands
meta import Lean.Parser.Term
import Init.Data

namespace Lean.Fmt

/-- Formats the `<mod> with <props>` widget instance specification, prefixed by `head`. -/
public def fmtWidgetInstanceSpec
    (head : TaggedDoc) (mod : TSyntax `ident) (withTk? : Option Syntax)
    (props? : Option (TSyntax `term))
    : FmtM TaggedDoc := do
  let mod ← fmt mod
  let withTk? ← fmt? withTk?
  let props? ← fmt? props?
  let lhs := Layouts.pseudoApplication #[head, mod]
  let «with» := Layouts.keywordPrefixedTerm withTk? props?
  return Layouts.blocks #[lhs, «with»]

@[builtin_fmt Lean.Widget.widgetCmd]
public def fmtWidgetCmd : Fmt := fun
  | `(Lean.Widget.widgetCmd| #widget%$widgetTk $mod:ident $[with%$withTk? $props?:term]?) => do
    fmtWidgetInstanceSpec (← fmt widgetTk) mod withTk? props?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Widget.addWidgetSpec]
public def fmtAddWidgetSpec : Fmt := fun
  | `(Lean.Widget.addWidgetSpec| $attrKind:attrKind $mod:ident $[with%$withTk? $props?:term]?) => do
    fmtWidgetInstanceSpec (← fmt attrKind) mod withTk? props?
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Widget.eraseWidgetSpec]
public def fmtEraseWidgetSpec : Fmt := fun
  | `(Lean.Widget.eraseWidgetSpec| -%$minusTk $mod:ident) => do
    let minusTk ← fmt minusTk
    let mod ← fmt mod
    return Layouts.prefixOperator minusTk mod .withoutSpacing
  | _ =>
    throw .partialFormatter

@[builtin_fmt Lean.Widget.showWidgetSpec]
public def fmtShowWidgetSpec : Fmt := fun
  | `(Lean.Widget.showWidgetSpec| $spec:addWidgetSpec) => fmt spec
  | `(Lean.Widget.showWidgetSpec| $spec:eraseWidgetSpec) => fmt spec
  | _ => throw .partialFormatter

@[builtin_fmt Lean.Widget.showPanelWidgetsCmd]
public def fmtShowPanelWidgetsCmd : Fmt := fun
  | `(Lean.Widget.showPanelWidgetsCmd|
      show_panel_widgets%$showTk [%$lbTk $specs:showWidgetSpec,* ]%$rbTk) => do
    let showTk ← fmt showTk
    let lbTk ← fmt lbTk
    let specs ← fmtTSepArray specs
    let rbTk ← fmt rbTk
    let specs := Layouts.collection lbTk specs rbTk
    return Layouts.pseudoApplication #[showTk, specs]
  | _ =>
    throw .partialFormatter
