/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
meta import Lean.Data.Html.Syntax
public import Lean.Data.Html.Syntax
meta import Lean.Elab.Term
public import Lean.Elab.Term
meta import Lean.Data.Html.Basic
public import Lean.Data.Html.Basic

set_option doc.verso true

namespace Lean.Html.Syntax

open Lean Elab Term Meta

meta def elabAttrVal (stx : AttrVal) : TermElabM Expr := withRef stx do
  match ← stx.view with
  | .str s | .interp s => elabTermEnsuringType s (Expr.const ``String [])

/-- Returns {lit}`.inl (attr : (String × String))`
or {lit}`.inr (attrs : Array (String × String))`. -/
meta def elabAttr (stx : Attr) : TermElabM (Expr ⊕ Expr) := withRef stx do
  let strType := Expr.const ``String []
  let pairType := mkApp2 (.const ``Prod [0, 0]) strType strType
  let arrayType := Expr.app (.const ``Array [0]) pairType
  match ← stx.view with
  | .val name val =>
    let name ← name.view
    let val ← elabAttrVal val
    return .inl <| mkApp4 (.const ``Prod.mk [0, 0]) strType strType (toExpr name) val
  | .bool name =>
    let name ← name.view
    return .inl <| mkApp4 (.const ``Prod.mk [0, 0]) strType strType (toExpr name) (toExpr "")
  | .interp t =>
    let t ← elabTermEnsuringType t pairType
    return .inl t
  | .interpMany t =>
    let t ← elabTermEnsuringType t arrayType
    return .inr t

meta def elabAttrs (stxs : Array Attr) : TermElabM Expr := do
  let strType := .const ``String []
  let pairType := mkApp2 (.const ``Prod [0, 0]) strType strType
  let mut attrs : Expr ← mkArrayLit pairType []
  for attr in stxs do
    match ← elabAttr attr with
    | .inl pair =>
      attrs := mkApp3 (.const ``Array.push [0]) pairType attrs pair
    | .inr pairs =>
      attrs := mkApp3 (.const ``Array.append [0]) pairType attrs pairs
  return attrs

meta partial def elabContent (stx : Content) : TermElabM (Option Expr) := withRef stx do
  match ← stx.view with
  | .element tagName attrs children =>
    if isVoidElement tagName then
      if h : 0 < children.size then
        let hint ←
          let some ⟨start, _⟩ := stx.raw.getRange? | pure m!""
          let some ⟨stop, _⟩ := children[0].raw.getRange? | pure m!""
          let src := (← getFileMap).source
          let noChildren := start.extract src (stop.prev src)
          MessageData.hint m!"Remove children" #[noChildren ++ "/>"]
        throwErrorAt children[0] m!"Void tag `<{tagName}>` cannot have children{hint}"
    let attrs ← elabAttrs attrs
    let children ←
      if h : children.size = 1 then
        let c ← elabContent children[0]
        pure <| c.getD (.const ``Html.empty [])
      else
        let children ← children.filterMapM elabContent
        let children ← mkArrayLit (.const ``Html []) children.toList
        pure <| .app (.const ``Html.ofArray []) children
    return mkApp3 (.const ``Html.element []) (toExpr tagName) attrs children
  | .text t =>
    let t ← t.view
    return mkApp (.const ``Html.text []) (toExpr t)
  | .interp val =>
    elabTermEnsuringType val (Expr.const ``Html [])
  | .comment .. => return none

/-! # html% -/

syntax "html%{" lean_html_syntax* "}" : term

elab_rules : term
  | `(term| html%{ $h:lean_html_syntax }) => withRef h do
    return (← elabContent h).getD (.const ``Html.empty [])
  | `(term| html%{ $hs:lean_html_syntax* }) => do
    let hs ← hs.filterMapM fun (h : Content) => withRef h <| elabContent h
    let hs ← mkArrayLit (.const ``Html []) hs.toList
    return .app (.const ``Html.ofArray []) hs
