/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
public meta import Lean.Data.Html.Syntax
public meta import Lean.Elab.Term
import Lean.Data.Html.Basic

set_option doc.verso true

namespace Lean.Elab.Html

open Lean Elab Term Meta
open Html Syntax

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
    let q ← `(ForIn.toArray (α := String × String) $t)
    let t ← elabTermEnsuringType q arrayType
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

meta partial def elabContent (stx : Content) : TermElabM Expr := withRef stx do
  let mut es : Array Expr := #[]
  for it in ← stx.view do
    withRef it.getSyntax do←
    match it with
    | .element elemStx startTag attrs children? =>
      let tagName ← startTag.view
      if isVoidElement tagName then
        if let some children := children? then
          let hint ←
            let some ⟨start, _⟩ := stx.raw.getRange? | pure m!""
            let some ⟨stop, _⟩ := children.raw.getRange? | pure m!""
            let src := (← getFileMap).source
            let noChildren := start.extract src (stop.prev src)
            MessageData.hint m!"Remove children" #[noChildren ++ "/>"]
          throwErrorAt elemStx m!"Void element `{tagName}` cannot have children{hint}"
      let attrs ← elabAttrs attrs
      let children? ← children?.mapM elabContent
      let e := mkApp3 (.const ``Html.element []) (toExpr tagName) attrs <|
        children?.getD (.const ``Html.empty [])
      es := es.push e
    | .text t =>
      let t ← t.view
      let e := mkApp (.const ``Html.text []) (toExpr t)
      es := es.push e
    | .interp val =>
      let e ← elabTermEnsuringType val (Expr.const ``Html [])
      es := es.push e
    | .comment .. => pure ()
  match es with
  | #[] => return .const ``Html.empty []
  | _ =>
    let children ← mkArrayLit (.const ``Html []) es.toList
    return .app (.const ``Html.ofArray []) children

syntax "html%{" content "}" : term

elab_rules : term
  | `(term| html%{ $h:content }) => elabContent h

end Lean.Elab.Html
