/-
Copyright (c) 2021 Wojciech Nawrocki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Wojciech Nawrocki, Sebastian Ullrich
-/
import Lean.Data.Json.FromToJson
import Lean.Parser

/-! This module defines:
- a representation of HTML trees
- together with a JSX-like DSL for writing them
- and widget support for visualizing any type as HTML. -/

namespace Lean.Widget

inductive Html where
  -- TODO(WN): it's nameless for shorter JSON; re-add names when we have deriving strategies for From/ToJson
  -- element (tag : String) (attrs : Array HtmlAttribute) (children : Array Html)
  | element : String → Array (String × String) → Array Html → Html
  | text : String → Html
  deriving Repr, BEq, Inhabited, FromJson, ToJson

instance : Coe String Html :=
  ⟨Html.text⟩

open Parser PrettyPrinter

declare_syntax_cat jsxElement
declare_syntax_cat jsxChild

-- TODO(WN): where `group`? where `symbol`? why?
def jsxAttrVal : Parser := strLit <|> group (symbol "{" >> termParser >> "}")
def jsxAttr : Parser := ident >> symbol "=" >> jsxAttrVal

syntax "<" ident jsxAttr* "/>" : jsxElement
syntax "<" ident jsxAttr* ">" jsxChild* "</" ident ">" : jsxElement

-- JSXTextCharacter : SourceCharacter but not one of {, <, > or }
def jsxText : Parser :=
  withAntiquot (mkAntiquot "jsxText" `jsxText) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (not ∘ "{<>}$".contains) "expected JSX text" c s
      mkNodeToken `jsxText startPos c s }

@[combinatorFormatter Lean.Widget.jsxText] def jsxText.formatter : Formatter := pure ()
@[combinatorParenthesizer Lean.Widget.jsxText] def jsxText.parenthesizer : Parenthesizer := pure ()

syntax jsxText      : jsxChild
syntax "{" term "}" : jsxChild
syntax jsxElement   : jsxChild

syntax:max jsxElement : term

macro_rules
  | `(<$n $[$ns = $vs]* />) =>
    let ns := ns.map (quote <| toString ·.getId)
    let vs := vs.map fun
      | `(jsxAttrVal| $s:strLit) => s
      | `(jsxAttrVal| { $t:term }) => t
      | _ => unreachable!
    `(Html.element $(quote <| toString n.getId) #[ $[($ns, $vs)],* ] #[])
  | `(<$n $[$ns = $vs]* >$cs*</$m>) =>
    if n.getId == m.getId then do
      let ns := ns.map (quote <| toString ·.getId)
      let vs := vs.map fun
        | `(jsxAttrVal| $s:strLit) => s
        | `(jsxAttrVal| { $t:term }) => t
        | _ => unreachable!
      let cs ← cs.mapM fun
        | `(jsxChild|$t:jsxText)    => `(Html.text $(quote t[0].getAtomVal!))
        -- TODO(WN): elab as list of children if tyipe is `t Html` where `Foldable t`
        | `(jsxChild|{$t})          => t
        | `(jsxChild|$e:jsxElement) => `($e:jsxElement)
        | _                         => unreachable!
      let tag := toString n.getId
      `(Html.element $(quote tag) #[ $[($ns, $vs)],* ] #[ $[$cs],* ])
    else Macro.throwError ("expected </" ++ toString n.getId ++ ">")

/-- A type which implements `ToHtmlFormat` will be visualized
as the resulting HTML in editors which support it. -/
class ToHtmlFormat (α : Type u) where
  formatHtml : α → Html

end Lean.Widget
