/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Nawrocki
-/
module

prelude
public import Init.Data.Array.GetLit
public import Init.Data.Array.Mem
public import Init.Dynamic

public import Lean.Data.Json.Elab

set_option doc.verso true

public section

namespace Lean

/-! # HTML trees -/

/-- A forest of HTML trees.

Analogous to React's [Fragment](https://react.dev/reference/react/Fragment). -/
inductive Html where
  /-- An element with the given tag, attributes, and children. -/
  | element (tag : String) (attrs : Array (String × String)) (children : Html)
  /-- Textual content. -/
  | text : String → Html
  /-- Unescaped, raw HTML content. -/
  | raw : String → Html
  /-- A sequence of HTML values. -/
  | seq : Array Html → Html
  deriving Repr, Inhabited, BEq, Hashable, TypeName

namespace Html

/-- The empty HTML forest. -/
@[suggest_for Lean.Html.nil Lean.Html.none]
def empty : Html := .seq #[]

/-- If {name}`escape` is {lean}`true`,
then characters such as {lean}`'&'` are escaped
to entities such as {lean}`"&amp;"` during rendering.-/
def ofString (escape : Bool) : String → Html :=
  if escape then text else raw

instance : Coe String Html := ⟨.text⟩

/-- Appends two HTML forests. -/
def append : Html → Html → Html
  | .seq #[], h        => h
  | h,        .seq #[] => h
  | .seq xs,  .seq ys  => .seq (xs ++ ys)
  | .seq xs,  other    => .seq (xs.push other)
  | other,    .seq ys  => .seq (#[other] ++ ys)
  | x,        y        => .seq #[x, y]

instance : Append Html := ⟨.append⟩

/-- Merges a collection of HTML values by appending them.

Equivalent to {name}`Html.seq`, but may produce a more compact representation. -/
@[suggest_for Lean.Html.ofArray Lean.Html.ofList]
def ofCollection {ρ : Type w} [ForIn Id ρ Html] (hs : ρ) : Html := Id.run do
  let mut out := .empty
  for h in hs do
    out := out ++ h
  return out

instance : Coe (Array Html) Html := ⟨ofCollection⟩
instance : Coe (List Html) Html := ⟨ofCollection⟩

/-- A compact JSON encoding of {name}`Html`. -/
instance : ToJson Html where
  toJson := to
where
  to
    | .text t => .str t
    | .raw r => json%{r: $r}
    | .element tag attrs children =>
      let attrs : Array Json := attrs.map fun (k, v) => .arr #[.str k, .str v]
      json%{t: $tag, a: $attrs, c: $(to children)}
    | .seq hs => .arr (hs.map to)

partial instance : FromJson Html where
  fromJson? j :=
    try
      from? j
    catch e =>
      throw s!"Failed to deserialize HTML from JSON {j.compress}: {e}"
where
  from?
    | .str s => return .text s
    | .arr j => return .seq (← j.mapM from?)
    | j@(.obj o) => do
      if let some tag := o["t"]? then
        let .str tag := tag | throw s!"Expected a string, got: {tag.compress}"
        let attrs ← j.getObjValAs? (Array Json) "a"
        let attrs ← attrs.mapM fun kv => do
          let .arr #[.str k, .str v] := kv
            | throw s!"Expected an array of two strings, got: {kv.compress}"
          return (k, v)
        let children ← j.getObjVal? "c" >>= from?
        return .element tag attrs children
      else if let some r := o["r"]? then
        let .str r := r | throw s!"Expected a string, got: {r.compress}"
        return .raw r
      else
        throw s!"Expected key \"t\" or key \"r\" in: {j.compress}"
    | j => throw s!"Expected a string, an object, or an array, got: {j.compress}"

open Syntax in
partial instance : Quote Html `term where
  quote := q
where
  q
    | .element tag attrs children =>
      let : Quote Html := ⟨q⟩
      mkCApp ``Html.element #[quote tag, quote attrs, quote children]
    | .text t =>
      mkCApp ``Html.text #[quote t]
    | .raw r =>
      mkCApp ``Html.raw #[quote r]
    | .seq s =>
      letI : Quote Html `term := ⟨q⟩
      mkCApp ``Html.seq #[quote s]

/-- Rewrites the forest by using {name}`fn` to transform every node.
Traversal proceeds in post-order:
{name}`fn` receives {name}`element` and {name}`seq` nodes with already-rewritten children. -/
partial def rewritePostM [Monad m] (fn : Html → m Html) : Html → m Html
  | .element tag attrs children => do
    let children' ← rewritePostM fn children
    fn (.element tag attrs children')
  | .seq s => do
    let s' ← s.mapM (rewritePostM fn)
    fn (.seq s')
  | h => fn h

/-- Rewrites the forest by using {name}`fn` to transform every node.
Traversal proceeds in post-order:
{name}`fn` receives {name}`element` and {name}`seq` nodes with already-rewritten children. -/
partial def rewritePost [Monad m] (fn : Html → Html) (h : Html) : Html :=
  rewritePostM (m := Id) fn h |>.run

end Lean.Html
