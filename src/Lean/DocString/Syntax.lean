/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module

prelude

import Init.Prelude
import Init.Notation
public import Lean.Parser.Types
import Lean.Syntax
import Lean.Parser.Extra
public import Lean.Parser.Term
meta import Lean.Parser.Term


/-!

This module contains an internal syntax that's used to represent documents.

Ordinarily, a syntax declaration is used to extend the Lean parser. The parser produces `Syntax`,
which is flexible enough to represent essentially anything. However, each syntax declaration will
produce parsed syntax trees with a predictable form, and these syntax trees can be matched using
quasiquotation patterns. In other words, syntax declarations really do all of the following:

 * They extend Lean's parser
 * They establish expectations for valid subsets of `Syntax`
 * They provide a way to pattern-match against the valid `Syntax` that they induce

The syntax declarations in this module are used somewhat differently. They're not generally intended
for direct use with the Lean parser, because the concrete syntax of Verso documents falls outside
what can be implemented with Lean's parsing framework. Thus, Verso has a separate parser, written
using the lower-level parts of Lean's parser. These syntax declarations are, however, a
specification for the syntax trees produced by said parser. The Verso parser is in the module
`Lean.DocString.Parser`. Specifying the Verso document syntax as is done here also allows
quasiquotation patterns that match against the output of the Verso parser.

Importantly, Lean quasiquotation patterns do not match the string contents of atoms. This means that
the Verso parser may produce a node of kind `` `Lean.Doc.Syntax.li `` in which the first atom is
`"1."` rather than `"*'` when parsing an ordered list.

Parsed Verso documents are transformed into Lean syntax that represents Verso document ASTs (see
module `Lean.DocString.Types`). This process potentially invokes user-written metaprograms - while
Verso's concrete syntax is not extensible, roles, directives and code blocks all contain explicit
hooks for extensibility. This translation step is defined in the module `Lean.DocString.Elab`.

-/

open Lean.Parser (rawIdent)

namespace Lean.Doc.Syntax

public section

/-- Argument values -/
declare_syntax_cat arg_val
scoped syntax (name:=arg_str) str : arg_val
scoped syntax (name:=arg_ident) ident : arg_val
scoped syntax (name:=arg_num) num : arg_val

/-- Arguments -/
declare_syntax_cat doc_arg
/-- Anonymous positional arguments -/
scoped syntax (name:=anon) arg_val : doc_arg
/-- Named arguments -/
scoped syntax (name:=named) "(" ident " := " arg_val ")": doc_arg
/-- Named arguments, without parentheses. -/
scoped syntax (name:=named_no_paren) ident " := " arg_val : doc_arg
/-- Boolean flags, turned on -/
scoped syntax (name:=flag_on) "+" ident : doc_arg
/-- Boolean flags, turned off -/
scoped syntax (name:=flag_off) "-" ident : doc_arg

/-- Link targets, which may be URLs or named references -/
declare_syntax_cat link_target
/-- A reference to a URL -/
scoped syntax (name:=url) "(" str ")" : link_target
/-- A named reference -/
scoped syntax (name:=ref) "[" str "]" : link_target

/--
Verso inline objects. These are part of the ordinary text flow of a paragraph.

This syntax uses the following conventions:
 * Sequences of inline items are in square brackets
 * Literal data, like strings or numbers, are in parentheses
 * Verso metaprogram names and arguments are in curly braces
-/
declare_syntax_cat inline
scoped syntax (name:=text) str : inline
/-- Emphasis (often rendered as italics) -/
scoped syntax (name:=emph) "_[" inline* "]" : inline
/-- Bold emphasis   -/
scoped syntax (name:=bold) "*[" inline* "]" : inline
/-- Link -/
scoped syntax (name:=link) "link[" inline* "]" link_target : inline
/-- Image -/
scoped syntax (name:=image) "image(" str ")" link_target : inline
/-- A footnote use -/
scoped syntax (name:=footnote) "footnote(" str ")" : inline
/-- Line break -/
scoped syntax (name:=linebreak) "line!" str : inline
/-- Literal code. If the first and last characters are space, and it contains at least one non-space
  character, then the resulting string has a single space stripped from each end.-/
scoped syntax (name:=code) "code(" str ")" : inline
/-- A _role_: an extension to the Verso document language in an inline position -/
scoped syntax (name:=role) "role{" ident doc_arg* "}" "[" inline* "]"  : inline
/-- Inline mathematical notation (equivalent to LaTeX's `$` notation) -/
scoped syntax (name:=inline_math) "\\math" code : inline
/-- Display-mode mathematical notation -/
scoped syntax (name:=display_math) "\\displaymath" code : inline

/--
Block-level elements, such as paragraphs, headers, and lists.

Conventions:
 * When there's concrete syntax that can be written as Lean atoms, do so (code blocks are ` ``` `,
   directives `:::`)
 * When Verso's syntax requires a newline, use `|` because `"\n"` is not a valid Lean token
 * Directive bodies are in `{` and `}` to avoid quotation parsing issues with `:::` ... `:::`
 * If there's no concrete syntax per se, such as for paragraphs or lists, use a name with brackets
   and braces
 * Use parentheses around required literals, such as the starting number of an ordered list
 * Use square brackets around sequences of literals
 * Use curly braces around blocks or lists items (because names and arguments a la roles are always
   newline-separated for directives and code)
-/
declare_syntax_cat block

/-- Items from both ordered and unordered lists -/
declare_syntax_cat list_item
/-- List item -/
syntax (name:=li) "*" block* : list_item

/-- A description of an item -/
declare_syntax_cat desc_item
/-- A description of an item -/
scoped syntax (name:=desc) ":" inline* "=>" block* : desc_item

scoped syntax (name:=para) "para[" inline+ "]" : block
/-- Unordered List -/
scoped syntax (name:=ul) "ul{" list_item* "}" : block
/-- Definition list -/
scoped syntax (name:=dl) "dl{" desc_item* "}" : block
/-- Ordered list -/
scoped syntax (name:=ol) "ol(" num ")" "{" list_item* "}" : block
/-- Literal code -/
scoped syntax (name:=codeblock) "```" (ident doc_arg*)? "|" str "```" : block
/-- Quotation -/
scoped syntax (name:=blockquote) ">" block* : block
/-- A link reference definition -/
scoped syntax (name:=link_ref)  "[" str "]:" str : block
/-- A footnote definition -/
scoped syntax (name:=footnote_ref) "[^" str "]:" inline* : block
/-- Custom directive -/
scoped syntax (name:=directive) ":::" rawIdent doc_arg* "{" block:max* "}" : block
/-- A header -/
scoped syntax (name:=header) "header(" num ")" "{" inline+ "}" : block
open Lean.Parser.Term in

open Lean.Parser Term in
meta def metadataContents : Parser :=
  structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))

/-- Metadata for this section, defined by the current genre -/
scoped syntax (name:=metadata_block) "%%%" metadataContents "%%%" : block

/-- A block-level command -/
scoped syntax (name:=command) "command{" rawIdent doc_arg* "}" : block
