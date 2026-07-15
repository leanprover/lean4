/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: E.W.Ayers, Wojciech Nawrocki
-/
module

prelude
public meta import Lean.Widget.UserWidget
public import Init.Notation
import Lean.Attributes

public section

namespace Lean.Widget
open Meta Elab

/-! ## `show_panel_widgets` command -/

syntax widgetInstanceSpec := ident ("with " term)?

private meta def elabWidgetInstanceSpecAux (mod : Ident) (props : Term) : TermElabM Expr := do
  Term.elabTerm (expectedType? := mkConst ``WidgetInstance) <| ← `(
    { id := $(quote mod.getId)
      javascriptHash := (ToModule.toModule $mod).javascriptHash
      props := Server.RpcEncodable.rpcEncode $props })

meta def elabWidgetInstanceSpec : TSyntax ``widgetInstanceSpec → TermElabM Expr
  | `(widgetInstanceSpec| $mod:ident) => do
    elabWidgetInstanceSpecAux mod (← ``(Json.mkObj []))
  | `(widgetInstanceSpec| $mod:ident with $props:term) => do
    elabWidgetInstanceSpecAux mod props
  | _ => throwUnsupportedSyntax

syntax addWidgetSpec := Parser.Term.attrKind widgetInstanceSpec
syntax eraseWidgetSpec := "-" ident
syntax showWidgetSpec := addWidgetSpec <|> eraseWidgetSpec
/-- Use `show_panel_widgets [<widget>]` to mark that `<widget>`
should always be displayed, including in downstream modules.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works.

Use `show_panel_widgets [<widget> with <props>]`
to specify the `<props>` that the widget should be given
as arguments.

Use `show_panel_widgets [local <widget> (with <props>)?]` to mark it
for display in the current section, namespace, or file only.

Use `show_panel_widgets [scoped <widget> (with <props>)?]` to mark it
for display only when the current namespace is open.

Use `show_panel_widgets [-<widget>]` to temporarily hide a previously shown widget
in the current section, namespace, or file.
Note that persistent erasure is not possible, i.e.,
`-<widget>` has no effect on downstream modules. -/
syntax (name := showPanelWidgetsCmd) "show_panel_widgets " "[" sepBy1(showWidgetSpec, ", ") "]" : command

open Command in
@[command_elab showPanelWidgetsCmd] meta def elabShowPanelWidgetsCmd : CommandElab
  | `(show_panel_widgets [ $ws ,*]) => liftTermElabM do
    for w in ws.getElems do
      match w with
      | `(showWidgetSpec| - $mod:ident) =>
        let mod : Term ← ``(ToModule.toModule $mod)
        let mod : Expr ← Term.elabTerm (expectedType? := mkConst ``Module) mod
        let mod : Module ← evalModule mod
        erasePanelWidget mod.javascriptHash
      | `(showWidgetSpec| $attr:attrKind $spec:widgetInstanceSpec) =>
        let attr ← liftMacroM <| toAttributeKind attr
        let wiExpr ← elabWidgetInstanceSpec spec
        let wi ← evalWidgetInstance wiExpr
        if let .local := attr then
          addPanelWidgetLocal wi
        else
          let name ← mkFreshUserName (wi.id ++ `_instance)
          let wiExpr ← instantiateMVars wiExpr
          if wiExpr.hasMVar then
            throwError "failed to compile expression, it contains metavariables{indentExpr wiExpr}"
          addAndCompile <| Declaration.defnDecl {
            name
            levelParams := []
            type := mkConst ``WidgetInstance
            value := wiExpr
            hints := .opaque
            safety := .safe
          }
          if let .global := attr then
            addPanelWidgetGlobal wi.javascriptHash name
          else
            addPanelWidgetScoped wi.javascriptHash name
      | _ => throwUnsupportedSyntax
  | _ => throwUnsupportedSyntax

/-! ## `#widget` command -/

/-- Use `#widget <widget>` to display a panel widget,
and `#widget <widget> with <props>` to display it with the given props.
Useful for debugging widgets.

The type of `<widget>` must implement `Widget.ToModule`,
and the type of `<props>` must implement `Server.RpcEncodable`.
In particular, `<props> : Json` works. -/
syntax (name := widgetCmd) "#widget " widgetInstanceSpec : command

open Command in
@[command_elab widgetCmd] meta def elabWidgetCmd : CommandElab
  | stx@`(#widget $s) => liftTermElabM do
    let wi : Expr ← elabWidgetInstanceSpec s
    let wi : WidgetInstance ← evalWidgetInstance wi
    savePanelWidgetInfo wi.javascriptHash wi.props stx
  | _ => throwUnsupportedSyntax
