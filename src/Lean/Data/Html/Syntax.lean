/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
public import Init.Data.String.Modify
meta import Lean.Data.Html.Syntax.Parsers
public import Lean.Data.Html.Syntax.Parsers
import Lean.Meta.Hint

set_option doc.verso true

/-!

Future top-level docstring for html%

- We require XHTML-style syntax: single tags must self-close (`<br>` doesn't parse, even though it does in HTML5),
and implied end tags are not supported (`<ul><li>abc<li>def</ul>` doesn't parse, even though it does in HTML5).
- Use `<script>{Html.raw ".."}</script>` for raw text elements
-/

public section

namespace Lean.Html.Syntax

-- Verbose names avoid conflicts with user-defined categories.
declare_syntax_cat lean_html_syntax

/-! # Attribute values -/

declare_syntax_cat lean_html_syntax_attr_val
syntax str : lean_html_syntax_attr_val
syntax group("{" term "}") : lean_html_syntax_attr_val

abbrev AttrVal := TSyntax `lean_html_syntax_attr_val

inductive AttrValView where
  | str (val : TSyntax `str)
  | interp (val : Term)
  deriving Inhabited

def AttrVal.view [Monad m] [MonadError m] : AttrVal → m AttrValView
  | `(lean_html_syntax_attr_val| $s:str) => return .str s
  | `(lean_html_syntax_attr_val| { $t }) => return .interp t
  | _ => Elab.throwUnsupportedSyntax

/-! # Attributes -/

declare_syntax_cat lean_html_syntax_attr
syntax attrName "=" lean_html_syntax_attr_val : lean_html_syntax_attr
syntax attrName : lean_html_syntax_attr
syntax group("{" term "}") : lean_html_syntax_attr
syntax group("{..." term "}") : lean_html_syntax_attr

abbrev Attr := TSyntax `lean_html_syntax_attr

inductive AttrView where
  | val (name : AttrName) (val : AttrVal)
  | bool (name : AttrName)
  | interp (val : Term)
  | interpMany (val : Term)
  deriving Inhabited

def Attr.view [Monad m] [MonadError m] : Attr → m AttrView
  | `(lean_html_syntax_attr| $n:attrName = $v) => return .val n v
  | `(lean_html_syntax_attr| $n:attrName) => return .bool n
  | `(lean_html_syntax_attr| { $t }) => return .interp t
  | `(lean_html_syntax_attr| {... $t }) => return .interpMany t
  | _ => Elab.throwUnsupportedSyntax

/-! # Top-level content -/

syntax (name := contentText) text : lean_html_syntax
syntax "<" lean_html_syntax_tag_name lean_html_syntax_attr* ">" lean_html_syntax* "</" lean_html_syntax_tag_name ">" : lean_html_syntax
syntax "<" lean_html_syntax_tag_name lean_html_syntax_attr* "/" ">" : lean_html_syntax
syntax group("{" term "}") : lean_html_syntax
-- TODO comment parser
-- syntax (name := htmlComment) "<!--" htmlCommentContents : lean_html_syntax

abbrev Content := TSyntax `lean_html_syntax

inductive ContentView where
  | element (tagName : String) (attrs : Array Attr) (children : Array Content)
  | text (t : Text)
  | interp (val : Term)
  -- | comment (c : CommentContents)

def Content.view : Content → CoreM ContentView
  | `(lean_html_syntax| $t:text) =>
    return .text t
  | `(lean_html_syntax| < $startTag $attrs* > $children* </ $endTag >) => do
    let startTagName ← TagName.view startTag
    let endTagName ← TagName.view endTag
    if endTagName.toLower != startTagName.toLower then
      let hint ← MessageData.hint m!"Replace with start tag" #[startTagName] (ref? := endTag)
      throwErrorAt endTag m!"Mismatched end tag, expected `{startTagName}` but got `{endTag}`{hint}"
    return .element startTagName attrs children
  | `(lean_html_syntax| <$startTagName $attrs*/>) =>
    return .element (← TagName.view startTagName) attrs #[]
  | `(lean_html_syntax| { $t }) =>
    return .interp t
  | _ =>
    Elab.throwUnsupportedSyntax

end Lean.Html.Syntax
