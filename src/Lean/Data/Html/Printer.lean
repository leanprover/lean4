/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki, David Thrane Christiansen
-/
module

prelude
public import Lean.Data.Html.Basic
import Init.Data.String.Modify
import Init.Data.String.Search
import Init.Data.Array.BinSearch

public section

namespace Lean.Html

/-- Array of void element names, sorted lexicographically.

Void elements are those that cannot have any child nodes.
These only have a start tag; end tags must not be specified.
See https://html.spec.whatwg.org/dev/syntax.html#void-elements -/
def voidElements : Array String :=
  #["area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "param", "source",
    "track", "wbr"]

section render_impl

private inductive RenderWorkItemKind where
  | html
  | attr
  | endAttrs
  | endElement
  | endVoidElement

private structure RenderWorkItemStack where
  kinds : Array RenderWorkItemKind
  htmls : Array Html
  strs  : Array String

namespace RenderWorkItemStack

@[inline]
private def pushKind (q : RenderWorkItemStack) (kind : RenderWorkItemKind) :
    RenderWorkItemStack := {
  q with kinds := q.kinds.push kind
}

@[inline]
private def pushHtml (q : RenderWorkItemStack) (value : Html) :
    RenderWorkItemStack := {
  q with htmls := q.htmls.push value
}

@[inline]
private def pushStr (q : RenderWorkItemStack) (str : String) :
    RenderWorkItemStack := {
  q with strs := q.strs.push str
}

@[inline]
private def popKind (q : RenderWorkItemStack) (h : q.kinds.size ≠ 0) :
    RenderWorkItemKind × RenderWorkItemStack :=
  let kind := q.kinds[q.kinds.size - 1]
  let q := { q with kinds := q.kinds.pop }
  (kind, q)

@[inline]
private def popHtml! (q : RenderWorkItemStack) :
    Html × RenderWorkItemStack :=
  let value := q.htmls[q.htmls.size - 1]!
  let q := { q with htmls := q.htmls.pop }
  (value, q)

@[inline]
private def popStr! (q : RenderWorkItemStack) :
    String × RenderWorkItemStack :=
  let str := q.strs[q.strs.size - 1]!
  let q := { q with strs := q.strs.pop }
  (str, q)

end RenderWorkItemStack

/-- Renders into a string to be consumed by browsers.
The input's structure is respected as much as possible; no whitespace is added or removed.

The output complies with [HTML5 syntax](https://html.spec.whatwg.org/dev/syntax.html),
and is compatible with [XML syntax for HTML](https://html.spec.whatwg.org/dev/xhtml.html)
in the following ways:
- Child-free void elements are rendered as self-closing tags.
  - (Spec-violating) void elements with children are rendered like normal elements.
- Attribute values are always quoted. -/
partial def render (h : Html) : String :=
  go "" {
    kinds := #[.html]
    htmls := #[h]
    strs := #[]
  }
where
  go (acc : String) (q : RenderWorkItemStack) : String :=
    if h : q.kinds.size = 0 then
      acc
    else
      let (kind, q) := q.popKind h
      match kind with
      | .html =>
        let (h, q) := q.popHtml!
        match h with
        | .element tag attrs children =>
          let q :=
            if let .seq #[] := children then
              if voidElements.binSearchContains tag.toLower (· < ·) then
                q.pushKind .endVoidElement
              else
                let q := q.pushKind .endElement |>.pushStr tag
                q.pushKind .endAttrs
            else
              let q := q.pushKind .endElement |>.pushStr tag
              let q := q.pushKind .html |>.pushHtml children
              q.pushKind .endAttrs
          let q := attrs.foldr (init := q) fun (k, v) q =>
            q.pushKind .attr |>.pushStr v |>.pushStr k
          go (acc ++ s!"<{tag}") q
        | .text t =>
          go (acc ++ escapeText t) q
        | .raw r =>
          go (acc ++ r) q
        | .seq s =>
          go acc <| s.foldr (init := q) fun h q => q.pushKind .html |>.pushHtml h
      | .attr =>
        let (k, q) := q.popStr!
        let (v, q) := q.popStr!
        go (acc ++ s!" {k}=\"{escapeAttr v}\"") q
      | .endAttrs =>
        go (acc.push '>') q
      | .endElement =>
        let (tag, q) := q.popStr!
        go (acc ++ s!"</{tag}>") q
      | .endVoidElement =>
        go (acc ++ "/>") q
  escapeAttr v := v.replace "&" "&amp;" |>.replace "\"" "&quot;"
  escapeText s := s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"

end render_impl

-- TODO: ToFormat and ToString instances with extra newlines/indentation for debug purposes

end Html
end Lean
