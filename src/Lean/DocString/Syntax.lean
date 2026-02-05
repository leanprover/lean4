/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

module

prelude
public import Lean.Parser.Term.Basic
public meta import Lean.Parser.Term.Basic


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
/-- Anonymous positional argument -/
@[builtin_doc]
scoped syntax (name:=anon) arg_val : doc_arg
/-- Named argument -/
@[builtin_doc]
scoped syntax (name:=named) "(" ident " := " arg_val ")": doc_arg
@[inherit_doc named, builtin_doc]
scoped syntax (name:=named_no_paren) ident " := " arg_val : doc_arg
/-- Boolean flag, turned on -/
@[builtin_doc]
scoped syntax (name:=flag_on) "+" ident : doc_arg
/-- Boolean flag, turned off -/
@[builtin_doc]
scoped syntax (name:=flag_off) "-" ident : doc_arg

/-- Link targets, which may be URLs or named references -/
declare_syntax_cat link_target
/-- A URL target, written explicitly. Use square brackets for a named target. -/
@[builtin_doc]
scoped syntax (name:=url) "(" str ")" : link_target
/-- A named reference to a URL defined elsewhere. Use parentheses to write the URL here. -/
@[builtin_doc]
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
/--
Emphasis, often rendered as italics.

Emphasis may be nested by using longer sequences of `_` for the outer delimiters. For example:
```
Remember: __always butter the _rugbrød_ before adding toppings!__
```
Here, the outer `__` is used to emphasize the instructions, while the inner `_` indicates the use of
a non-English word.
-/
@[builtin_doc]
scoped syntax (name:=emph) "_[" inline* "]" : inline
/--
Bold emphasis.

A single `*` suffices to make text bold. Using `_` for emphasis.

Bold text may be nested by using longer sequences of `*` for the outer delimiters.
-/
@[builtin_doc]
scoped syntax (name:=bold) "*[" inline* "]" : inline
/--
A link. The link's target may either be a concrete URL (written in parentheses) or a named URL
(written in square brackets).
-/
@[builtin_doc]
scoped syntax (name:=link) "link[" inline* "]" link_target : inline
/--
An image, with alternate text and a URL.

The alternate text is a plain string, rather than Verso markup.

The image URL may either be a concrete URL (written in parentheses) or a named URL (written in
square brackets).
-/

@[builtin_doc]
scoped syntax (name:=image) "image(" str ")" link_target : inline
/--
A footnote use site.

Footnotes must be defined elsewhere using the `[^NAME]: TEXT` syntax.
-/
@[builtin_doc]
scoped syntax (name:=footnote) "footnote(" str ")" : inline
scoped syntax (name:=linebreak) "line!" str : inline
/--
Literal code.

Code may begin with any non-zero number of backticks. It must be terminated with the same number,
and it may not contain a sequence of backticks that is at least as long as its starting or ending
delimiters.

If the first and last characters are space, and it contains at least one non-space character, then
the resulting string has a single space stripped from each end. Thus, ``` `` `x `` ``` represents
``"`x"``, not ``" `x "``.
-/
@[builtin_doc]
scoped syntax (name:=code) "code(" str ")" : inline
/--
A _role_: an extension to the Verso document language in an inline position.

Text is given a role using the following syntax: `{NAME ARGS*}[CONTENT]`. The `NAME` is an
identifier that determines which role is being used, akin to a function name. Each of the `ARGS` may
have the following forms:
* A value, which is a string literal, natural number, or identifier
* A named argument, of the form `(NAME := VALUE)`
* A flag, of the form `+NAME` or `-NAME`

The `CONTENT` is a sequence of inline content. If there is only one piece of content and it has
beginning and ending delimiters (e.g. code literals, links, or images, but not ordinary text), then
the `[` and `]` may be omitted. In particular, `` {NAME ARGS*}`x` `` is equivalent to
``{NAME ARGS*}[`x`]``.
-/
@[builtin_doc]
scoped syntax (name:=role) "role{" ident doc_arg* "}" "[" inline* "]"  : inline
/-- Inline mathematical notation (equivalent to LaTeX's `$` notation) -/
@[builtin_doc]
scoped syntax (name:=inline_math) "\\math" code : inline
/-- Display-mode mathematical notation -/
@[builtin_doc]
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
/-- A list item -/
@[builtin_doc]
syntax (name:=li) "*" block* : list_item

/-- A description of an item -/
declare_syntax_cat desc_item
/-- A description of an item -/
@[builtin_doc]
scoped syntax (name:=desc) ":" inline* "=>" block* : desc_item

/-- Paragraph -/
@[builtin_doc]
scoped syntax (name:=para) "para[" inline+ "]" : block
/-- Unordered List -/
@[builtin_doc]
scoped syntax (name:=ul) "ul{" list_item* "}" : block
/-- Description list -/
@[builtin_doc]
scoped syntax (name:=dl) "dl{" desc_item* "}" : block
/-- Ordered list -/
@[builtin_doc]
scoped syntax (name:=ol) "ol(" num ")" "{" list_item* "}" : block
/--
A code block that contains literal code.

Code blocks have the following syntax:
````
```(NAME ARGS*)?
CONTENT
```
````

`CONTENT` is a literal string. If the `CONTENT` contains a sequence of three or more backticks, then
the opening and closing ` ``` ` (called _fences_) should have more backticks than the longest
sequence in `CONTENT`. Additionally, the opening and closing fences should have the same number of
backticks.

If `NAME` and `ARGS` are not provided, then the code block represents literal text. If provided, the
`NAME` is an identifier that selects an interpretation of the block. Unlike Markdown, this name is
not necessarily the language in which the code is written, though many custom code blocks are, in
practice, named after the language that they contain. `NAME` is more akin to a function name. Each
of the `ARGS` may have the following forms:
* A value, which is a string literal, natural number, or identifier
* A named argument, of the form `(NAME := VALUE)`
* A flag, of the form `+NAME` or `-NAME`

The `CONTENT` is interpreted according to the indentation of the fences. If the fences are indented
`n` spaces, then `n` spaces are removed from the start of each line of `CONTENT`.
-/
@[builtin_doc]
scoped syntax (name:=codeblock) "```" (ident doc_arg*)? "|" str "```" : block
/--
A quotation, which contains a sequence of blocks that are at least as indented as the `>`.
-/
@[builtin_doc]
scoped syntax (name:=blockquote) ">" block* : block
/--
A named URL that can be used in links and images.
-/
@[builtin_doc]
scoped syntax (name:=link_ref)  "[" str "]:" str : block
/--
A footnote definition.
-/
@[builtin_doc]
scoped syntax (name:=footnote_ref) "[^" str "]:" inline* : block
/--
A _directive_, which is an extension to the Verso language in block position.

Directives have the following syntax:
```
:::NAME ARGS*
CONTENT*
:::
```

The `NAME` is an identifier that determines which directive is being used, akin to a function name.
Each of the `ARGS` may have the following forms:
* A value, which is a string literal, natural number, or identifier
* A named argument, of the form `(NAME := VALUE)`
* A flag, of the form `+NAME` or `-NAME`

The `CONTENT` is a sequence of block content. Directives may be nested by using more colons in
the outer directive. For example:
```
::::outer +flag (arg := 5)
A paragraph.
:::inner "label"
* 1
* 2
:::
::::
```

-/
@[builtin_doc]
scoped syntax (name:=directive) ":::" rawIdent doc_arg* "{" block:max* "}" : block
/--
A header

Headers must be correctly nested to form a tree structure. The first header in a document must
start with `#`, and subsequent headers must have at most one more `#` than the preceding header.
-/
@[builtin_doc]
scoped syntax (name:=header) "header(" num ")" "{" inline+ "}" : block

open Lean.Parser Term in
meta def metadataContents : Lean.Parser.Parser :=
  structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))

/--
Metadata for the preceding header.
-/
@[builtin_doc]
scoped syntax (name:=metadata_block) "%%%" metadataContents "%%%" : block

/--
A block-level command, which invokes an extension during documentation processing.

The `NAME` is an identifier that determines which command is being used, akin to a function name.
Each of the `ARGS` may have the following forms:
* A value, which is a string literal, natural number, or identifier
* A named argument, of the form `(NAME := VALUE)`
* A flag, of the form `+NAME` or `-NAME`
-/
@[builtin_doc]
scoped syntax (name:=command) "command{" rawIdent doc_arg* "}" : block
