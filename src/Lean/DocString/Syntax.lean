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
This module declares the syntax of Verso documents.

The concrete syntax falls outside what Lean's parsing framework can express, so Verso has a separate
parser, in `Lean.DocString.Parser`, written with the lower-level parts of Lean's parser. The node
kinds it produces are declared here, in `Lean.Doc.Parser`, together with the tokens that store
literal content and the accessors that decode them.

Consumers read this syntax through the views in `Lean.DocString.View`, which is the only place that
matches document syntax directly.

Elaboration turns a parsed document into Lean syntax for the Verso document AST of
`Lean.DocString.Types`, and may invoke user-written metaprograms on the way: the concrete syntax is
not extensible, but roles, directives, and code blocks are hooks for extension. That step is in
`Lean.Elab.DocString`.
-/

open Lean.Parser (rawIdent)

/-
The declarations in this namespace are a temporary bootstrapping encoding, produced by quotations
rather than by the parser. After a stage0 update they can be deleted, along with the migration
sections in `Lean.DocString.View` and `Lean.Elab.DocString` that convert between the two.
-/
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

end

end Lean.Doc.Syntax

namespace Lean.Doc.Parser

public section

/-!
The tokens that store literal Verso content. The Verso parser builds them itself, so each
declaration below supplies only the antiquotation that can be used in Lean syntax quasiquotations.
Its own name is the token's syntax node kind.
-/

open Lean.Parser in
/-- Literal text content. -/
def versoText : Parser := mkAntiquot "versoText" decl_name%

open Lean.Parser in
/-- The name of a footnote or a link reference. -/
def versoRef : Parser := mkAntiquot "versoRef" decl_name%

open Lean.Parser in
/-- The URL of a link or an image. -/
def versoLinkUrl : Parser := mkAntiquot "versoLinkUrl" decl_name%

open Lean.Parser in
/-- The URL that a link reference definition provides. -/
def versoLinkRefUrl : Parser := mkAntiquot "versoLinkRefUrl" decl_name%

open Lean.Parser in
/-- The alternate text of an image. -/
def versoImageAlt : Parser := mkAntiquot "versoImageAlt" decl_name%

open Lean.Parser in
/-- Literal inline code content. -/
def versoCode : Parser := mkAntiquot "versoCode" decl_name%

open Lean.Parser in
/-- Literal code block content. -/
def versoCodeBlock : Parser := mkAntiquot "versoCodeBlock" decl_name%

open Lean.Parser in
/-- One source line of code block content. -/
def versoCodeBlockLine : Parser := mkAntiquot "versoCodeBlockLine" decl_name%

end

end Lean.Doc.Parser

namespace Lean.Doc
open Lean.Doc.Parser

public section

/-!
The kinds of the tokens that store literal content, and the `TSyntax` types over them. A token
contains the source text exactly as written, keeping escape sequences, boundary spaces, and
indentation. The `getVerso*` accessors decode it.
-/

/-- Tokens that contain Verso text content. -/
def versoTextKind : SyntaxNodeKind := ``versoText

/-- The name of a Verso footnote or link reference name. -/
def versoRefKind : SyntaxNodeKind := ``versoRef

/-- The URL of a Verso link or image. -/
def versoLinkUrlKind : SyntaxNodeKind := ``versoLinkUrl

/-- The URL that a Verso link reference definition provides. -/
def versoLinkRefUrlKind : SyntaxNodeKind := ``versoLinkRefUrl

/-- The alternate text of a Verso image. -/
def versoImageAltKind : SyntaxNodeKind := ``versoImageAlt

/-- Tokens that contain Verso inline code. -/
def versoCodeKind : SyntaxNodeKind := ``versoCode

/-- The contents of a Verso code block. -/
def versoCodeBlockKind : SyntaxNodeKind := ``versoCodeBlock

/-- One source line inside a Verso code block. -/
def versoCodeBlockLineKind : SyntaxNodeKind := ``versoCodeBlockLine

/--
Text content in a Verso document. The token contains the source text with escape sequences
intact. Use `TSyntax.getVersoText` to decode it.
-/
abbrev VersoText := TSyntax ``versoText

/--
The name of a footnote or a link reference in a Verso document. Use `TSyntax.getVersoRefName` to
read it. These names may not contain `[`, `]`, `^`, newlines, or tabs.
-/
abbrev VersoRefName := TSyntax ``versoRef

/--
The URL of a link or an image in a Verso document. Use `TSyntax.getVersoLinkUrl` to read it.
-/
abbrev VersoLinkUrl := TSyntax ``versoLinkUrl

/--
The URL that a link reference definition provides in a Verso document. Use
`TSyntax.getVersoLinkRefUrl` to read it.
-/
abbrev VersoLinkRefUrl := TSyntax ``versoLinkRefUrl

/--
The alternate text of an image in a Verso document. Use `TSyntax.getVersoImageAlt` to read it.

It may contain `]` behind an escape character, and the escape remains part of the content.
-/
abbrev VersoImageAlt := TSyntax ``versoImageAlt

/--
Inline code content in a Verso document. The token contains the text between the backtick
delimiters, including boundary spaces. Use `TSyntax.getVersoCode` to decode it.
-/
abbrev VersoCode := TSyntax ``versoCode

/--
Code block content in a Verso document, with one `versoCodeBlockLine` token per source line. Use
`TSyntax.getVersoCodeBlock` to decode it.
-/
abbrev VersoCodeBlock := TSyntax ``versoCodeBlock

/--
A single source line of code block content in a Verso document. The token's leading whitespace is
the indentation of the code block. Indentation past that is part of the token's content.
-/
abbrev VersoCodeBlockLine := TSyntax ``versoCodeBlockLine

/--
The length of the longest run of backticks in `str`. A delimiter of inline code, and the fence of a
code block, is longer than every run of backticks in the content it surrounds.
-/
def longestBacktickRun (str : String) : Nat := Id.run do
  let mut best : Nat := 0
  let mut run : Nat := 0
  for c in str do
    if c == '`' then
      run := run + 1
      if run > best then best := run
    else run := 0
  best

/--
Whether `str` begins and ends with a space and contains a character other than a space.

In a code element, this sequence denotes the content with a space removed from each end. It can be
escaped by adding spaces to each end, so this function can be used to determine whether decoding or
encoding is necessary.
-/
def versoCodeBoundarySpaces (str : String) : Bool :=
  str.startsWith " " && str.endsWith " " && str.any (· != ' ')

/--
Removes the escaping backslashes from Verso content: `\c` denotes the character `c`.

Verso does not use escapes such as `\n` for newlines.
-/
private def unescapeVerso (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.startPos
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    iter := iter.next h
    if c == '\\' then
      if h : ¬iter.IsAtEnd then
        out := out.push (iter.get h)
        iter := iter.next h
    else
      out := out.push c
  out

/--
Escapes the characters of `value` that would otherwise end the content, so that decoding the result
gives `value` back. The escape character escapes itself.
-/
private def escapeVersoDelimited (delimiters : List Char) (value : String) : String :=
  value.foldl (init := "") fun out c =>
    if c == '\\' || c ∈ delimiters then out.push '\\' |>.push c else out.push c

/-- Escapes `value` so that `getVersoLinkUrl` reads it back unchanged. -/
def escapeVersoLinkUrl (value : String) : String := escapeVersoDelimited [')'] value

/-- Escapes `value` so that `getVersoImageAlt` reads it back unchanged. -/
def escapeVersoImageAlt (value : String) : String := escapeVersoDelimited [']'] value

end

end Lean.Doc

namespace Lean.TSyntax

public section

open Lean.Doc

/--
Decodes and returns the text that a Verso text token denotes, decoding escape sequences.
-/
def getVersoText (s : VersoText) : String :=
  unescapeVerso <| (Syntax.isLit? versoTextKind s.raw).getD ""

/--
Returns the text of a Verso text token as it was written, with its escape sequences intact.
-/
def getVersoTextSource (s : VersoText) : String :=
  (Syntax.isLit? versoTextKind s.raw).getD ""

/--
Decodes and returns the name that a Verso footnote or link reference token contains.
-/
def getVersoRefName (s : VersoRefName) : String :=
  (Syntax.isLit? versoRefKind s.raw).getD ""

/--
Returns the URL that a Verso link or image token contains, as it was written.
-/
def getVersoLinkUrl (s : VersoLinkUrl) : String :=
  unescapeVerso <| (Syntax.isLit? versoLinkUrlKind s.raw).getD ""

/--
Returns the URL that a Verso link reference definition token contains. These positions do not
support escape sequences.
-/
def getVersoLinkRefUrl (s : VersoLinkRefUrl) : String :=
  (Syntax.isLit? versoLinkRefUrlKind s.raw).getD ""

/--
Returns the alternate text that a Verso image token contains, as it was written.
-/
def getVersoImageAlt (s : VersoImageAlt) : String :=
  unescapeVerso <| (Syntax.isLit? versoImageAltKind s.raw).getD ""

/--
Decodes and returns the code that a Verso inline code token denotes.
-/
def getVersoCode (s : VersoCode) : String :=
  let str := (Syntax.isLit? versoCodeKind s.raw).getD ""
  if versoCodeBoundarySpaces str then str.drop 1 |>.dropEnd 1 |>.copy else str

/--
Returns the text of one source line inside a Verso code block.
-/
def getVersoCodeBlockLine (s : VersoCodeBlockLine) : String :=
  (Syntax.isLit? versoCodeBlockLineKind s.raw).getD ""

/--
Returns the source lines of a Verso code block, in order.
-/
def getVersoCodeBlockLines (s : VersoCodeBlock) :
    TSyntaxArray ``Parser.versoCodeBlockLine :=
  -- The repetition that reads the lines groups them in a null node.
  .mk s.raw[0].getArgs

/--
Returns the contents of a Verso code block, which are the texts of its lines in order.
-/
def getVersoCodeBlock (s : VersoCodeBlock) : String := Id.run do
  let mut out := ""
  for line in s.getVersoCodeBlockLines do
    out := out ++ line.getVersoCodeBlockLine
  out

end

end Lean.TSyntax

/-!
The kinds of the nodes that the Verso parser builds, grouped by syntax category as
`Lean.Parser.Term` and `Lean.Parser.Command` are. The tokens that store literal content are
declared above, with the accessors that decode them.
-/

namespace Lean.Doc.Parser

public section

namespace ArgVal

open Lean.Parser in
def str : Lean.Parser.Parser := nodeWithAntiquot "ArgVal.str" decl_name% Lean.Parser.strLit
open Lean.Parser in
def ident : Lean.Parser.Parser := nodeWithAntiquot "ArgVal.ident" decl_name% Lean.Parser.ident
open Lean.Parser in
def num : Lean.Parser.Parser := nodeWithAntiquot "ArgVal.num" decl_name% Lean.Parser.numLit

end ArgVal

open Lean.Parser in
/--
Argument values. Quotations may use antiquotations for any of the forms.
-/
def argVal : Lean.Parser.Parser :=
  withAntiquot (mkAntiquot "argVal" decl_name% (isPseudoKind := true)) <|
    ArgVal.str <|> ArgVal.ident <|> ArgVal.num

namespace Arg

open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.anon, builtin_doc]
def anon : Lean.Parser.Parser := nodeWithAntiquot "anon" decl_name% argVal
open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.named, builtin_doc]
def named : Lean.Parser.Parser :=
  nodeWithAntiquot "named" decl_name% ("(" >> Lean.Parser.ident >> " := " >> argVal >> ")")
open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.named_no_paren, builtin_doc]
def named_no_paren : Lean.Parser.Parser :=
  nodeWithAntiquot "named_no_paren" decl_name% (Lean.Parser.ident >> " := " >> argVal)
open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.flag_on, builtin_doc]
def flag_on : Lean.Parser.Parser :=
  nodeWithAntiquot "flag_on" decl_name% ("+" >> Lean.Parser.ident)
open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.flag_off, builtin_doc]
def flag_off : Lean.Parser.Parser :=
  nodeWithAntiquot "flag_off" decl_name% ("-" >> Lean.Parser.ident)

end Arg

open Lean.Parser in
/--
Arguments to a role, directive, command, or code block.
-/
def arg : Lean.Parser.Parser :=
  withAntiquot (mkAntiquot "arg" decl_name% (isPseudoKind := true)) <|
    Arg.named <|> Arg.flag_on <|> Arg.flag_off <|>
      atomic Arg.named_no_paren <|> Arg.anon

namespace LinkTarget

open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.url, builtin_doc]
def url : Lean.Parser.Parser :=
  nodeWithAntiquot "url" decl_name% ("(" >> versoLinkUrl >> ")")
open Lean.Parser in
@[inherit_doc Lean.Doc.Syntax.ref, builtin_doc]
def ref : Lean.Parser.Parser :=
  nodeWithAntiquot "ref" decl_name% ("[" >> versoRef >> "]")

end LinkTarget

open Lean.Parser in
/--
The target of a link or image.
-/
def linkTarget : Lean.Parser.Parser :=
  withAntiquot (mkAntiquot "linkTarget" decl_name% (isPseudoKind := true)) <|
    LinkTarget.url <|> LinkTarget.ref

open Lean.Parser in
/-- Matches the literal characters of `s`, producing a single atom that takes a position binder. -/
private def atomOf (s : String) : Lean.Parser.Parser :=
  tokenWithAntiquot {
    fn := rawFn (trailingWs := true) fun c st =>
      let chars := s.toList.foldl (init := (fun _ st => st : ParserFn))
        fun p ch => p >> satisfyFn (· == ch) ch.toString
      let st' := chars c st
      -- The characters are read one at a time, so a failure names the one that did not match. The
      -- atom is what was expected, and reporting it at the start says where it would have begun.
      if st'.hasError then st'.mkErrorAt s!"'{s}'" st.pos else st'
  }

open Lean.Parser in
/-- Matches a run of one or more `c`, producing a single atom. -/
private def charRun (ch : Char) : Lean.Parser.Parser :=
  tokenWithAntiquot {
    fn := rawFn (trailingWs := true) fun c st =>
      let st' := takeWhile1Fn (· == ch) s!"'{ch}'" c st
      if st'.hasError then st'.mkErrorAt s!"one or more '{ch}'" st.pos else st'
  }

open Lean.Parser in
/-- Matches a list item's marker, producing a single atom. -/
private def markerAtom : Lean.Parser.Parser :=
  tokenWithAntiquot {
    -- A single scan, so that nothing pushes a wrapper node beside the atom.
    fn := rawFn (trailingWs := true) fun c s =>
      if h : c.atEnd s.pos then s.mkEOIError
      else
        let ch := c.get' s.pos h
        if ch == '*' || ch == '-' || ch == '+' then s.next' c s.pos h
        else
          let s' := (takeWhile1Fn (·.isDigit) "'0'-'9'" >>
            satisfyFn (fun c => c == '.' || c == ')') "'.' or ')'") c s
          if s'.hasError then s'.mkErrorAt "a list marker" s.pos else s'
  }

open Lean.Parser in
/--
Metadata block contents, which are the fields of a structure instance. The Verso parser reads them
with `Lean.Doc.Parser.metadataContents`, so a quotation splices a node of the kind that produces.
-/
private def metadataContentsLit : Lean.Parser.Parser :=
  mkAntiquot "metadataContents" ``Lean.Parser.Term.structInstFields

open Lean.Parser in
/--
The sequence of `#` characters that introduces a header. Its length determines the header's level.
-/
def headerMarker : Lean.Parser.Parser :=
  nodeWithAntiquot "headerMarker" decl_name% (charRun '#')

open Lean.Parser in
/--
The marker that introduces a list item. An unordered list uses `*`, `-`, or `+`. An ordered list
uses a number followed by `.` or `)`.
-/
def listMarker : Lean.Parser.Parser := nodeWithAntiquot "listMarker" decl_name% markerAtom

open Lean.Parser in
/-- The run of `_` characters that delimits emphasis. -/
def emphDelimiter : Lean.Parser.Parser :=
  nodeWithAntiquot "emphDelimiter" decl_name% (charRun '_')

open Lean.Parser in
/-- The sequence of `*` characters that delimits bold text. -/
def boldDelimiter : Lean.Parser.Parser :=
  nodeWithAntiquot "boldDelimiter" decl_name% (charRun '*')

open Lean.Parser in
/--
The sequence of backticks that delimits inline code. Longer delimiters allow backticks in the
content.
-/
def codeDelimiter : Lean.Parser.Parser :=
  nodeWithAntiquot "codeDelimiter" decl_name% (charRun '`')

open Lean.Parser in
/--
The fence that surrounds a code block. Longer fences allow more backticks in the content.
-/
def codeBlockFence : Lean.Parser.Parser :=
  nodeWithAntiquot "codeBlockFence" decl_name% (charRun '`')

open Lean.Parser in
/--
The `$` that introduces inline mathematical notation. `$` begins an antiquotation, so a quotation
splices this atom in as `$m:inlineMathMarker`.
-/
def inlineMathMarker : Lean.Parser.Parser :=
  nodeWithAntiquot "inlineMathMarker" decl_name% (atomOf "$")

open Lean.Parser in
@[inherit_doc inlineMathMarker]
def displayMathMarker : Lean.Parser.Parser :=
  nodeWithAntiquot "displayMathMarker" decl_name% (atomOf "$$")

open Lean.Parser in
/-- The sequence `:` characters that delimits a directive. -/
def directiveDelimiter : Lean.Parser.Parser :=
  nodeWithAntiquot "directiveDelimiter" decl_name% (charRun ':')

open Lean.Parser in
/--
Inline code, used on its own and as the content of mathematical notation.
-/
private def inlineCode : Lean.Parser.Parser :=
  nodeWithAntiquot "code" `Lean.Doc.Parser.Inline.code (codeDelimiter >> versoCode >> codeDelimiter)

-- The inline productions are mutually recursive. Recursive `Parser` values cannot express that,
-- so the `*Quot` definitions below break the recursion at the `ParserFn` level.
open Lean.Parser in
mutual
  private partial def inlineQuot : ParserFn := fun c s =>
    -- Once an antiquotation parses, `withAntiquotFn` skips the alternatives. `para` and friends
    -- have no opening delimiter, so backtracking into them would let `$x` parse as an inline inside
    -- one of them. The ambiguity would then resolve against the writer's intent.
    let alts : Parser :=
      { fn := textQuot } <|> { fn := emphQuot } <|> { fn := boldQuot } <|> inlineCode <|>
      { fn := mathQuot } <|> { fn := linkQuot } <|> { fn := imageQuot } <|> { fn := footnoteQuot } <|>
      { fn := linebreakQuot } <|> { fn := roleQuot }
    withAntiquotFn (mkAntiquot "inline" `Lean.Doc.Parser.inline (isPseudoKind := true)).fn
      alts.fn (isCatAntiquot := true) c s

  private partial def textQuot : ParserFn :=
    (nodeWithAntiquot "text" `Lean.Doc.Parser.Inline.text versoText).fn

  private partial def emphQuot : ParserFn :=
    (nodeWithAntiquot "emph" `Lean.Doc.Parser.Inline.emph
      (emphDelimiter >> many (atomic { fn := inlineQuot }) >> emphDelimiter)).fn

  private partial def boldQuot : ParserFn :=
    (nodeWithAntiquot "bold" `Lean.Doc.Parser.Inline.bold
      (boldDelimiter >> many (atomic { fn := inlineQuot }) >> boldDelimiter)).fn

  private partial def displayMathQuot : ParserFn :=
    (nodeWithAntiquot "display_math" `Lean.Doc.Parser.Inline.display_math
      (displayMathMarker >> inlineCode)).fn

  private partial def inlineMathQuot : ParserFn :=
    (nodeWithAntiquot "inline_math" `Lean.Doc.Parser.Inline.inline_math
      (inlineMathMarker >> inlineCode)).fn

  private partial def mathQuot : ParserFn :=
    (atomic { fn := displayMathQuot } <|> ({ fn := inlineMathQuot } : Parser)).fn

  private partial def linkQuot : ParserFn :=
    (nodeWithAntiquot "link" `Lean.Doc.Parser.Inline.link
      (atomOf "[" >> many (atomic { fn := inlineQuot }) >> atomOf "]" >> linkTarget)).fn

  private partial def imageQuot : ParserFn :=
    (nodeWithAntiquot "image" `Lean.Doc.Parser.Inline.image
      (atomOf "![" >> versoImageAlt >> atomOf "]" >> linkTarget)).fn

  private partial def footnoteQuot : ParserFn :=
    (nodeWithAntiquot "footnote" `Lean.Doc.Parser.Inline.footnote
      (atomOf "[^" >> versoRef >> atomOf "]")).fn

  private partial def linebreakQuot : ParserFn :=
    (nodeWithAntiquot "linebreak" `Lean.Doc.Parser.Inline.linebreak (charRun '\n')).fn

  private partial def roleQuot : ParserFn :=
    (nodeWithAntiquot "role" `Lean.Doc.Parser.Inline.role
      (atomOf "{" >> Lean.Parser.ident >> many arg >> atomOf "}" >>
        -- Each bracket sits in a group, so that an omitted bracket is an empty group, which
        -- matches what the Verso parser produces.
        ((node nullKind (atomOf "[") >> many (atomic { fn := inlineQuot }) >>
           node nullKind (atomOf "]")) <|>
         (node nullKind skip >> many1 (atomic { fn := inlineQuot }) >> node nullKind skip)))).fn
end

namespace Inline

def text : Lean.Parser.Parser := { fn := textQuot }
@[inherit_doc Lean.Doc.Syntax.emph, builtin_doc]
def emph : Lean.Parser.Parser := { fn := emphQuot }
@[inherit_doc Lean.Doc.Syntax.bold, builtin_doc]
def bold : Lean.Parser.Parser := { fn := boldQuot }
@[inherit_doc Lean.Doc.Syntax.code, builtin_doc]
def code : Lean.Parser.Parser := inlineCode
@[inherit_doc Lean.Doc.Syntax.inline_math, builtin_doc]
def inline_math : Lean.Parser.Parser := { fn := inlineMathQuot }
@[inherit_doc Lean.Doc.Syntax.display_math, builtin_doc]
def display_math : Lean.Parser.Parser := { fn := displayMathQuot }
@[inherit_doc Lean.Doc.Syntax.link, builtin_doc]
def link : Lean.Parser.Parser := { fn := linkQuot }
@[inherit_doc Lean.Doc.Syntax.image, builtin_doc]
def image : Lean.Parser.Parser := { fn := imageQuot }
@[inherit_doc Lean.Doc.Syntax.footnote, builtin_doc]
def footnote : Lean.Parser.Parser := { fn := footnoteQuot }
def linebreak : Lean.Parser.Parser := { fn := linebreakQuot }
@[inherit_doc Lean.Doc.Syntax.role, builtin_doc]
def role : Lean.Parser.Parser := { fn := roleQuot }

end Inline

/-- Any inline element. -/
def inline : Lean.Parser.Parser := { fn := inlineQuot }

open Lean.Parser in
mutual
  private partial def blockQuot : ParserFn := fun c s =>
    let alts : Parser :=
      { fn := paraQuot } <|> { fn := ulQuot } <|> { fn := olQuot } <|> { fn := dlQuot } <|>
      { fn := blockquoteQuot } <|> { fn := codeblockQuot } <|> { fn := directiveQuot } <|>
      { fn := headerQuot } <|> { fn := linkRefQuot } <|> { fn := footnoteRefQuot } <|>
      { fn := metadataQuot } <|> { fn := commandQuot }
    withAntiquotFn (mkAntiquot "block" `Lean.Doc.Parser.block (isPseudoKind := true)).fn
      alts.fn (isCatAntiquot := true) c s

  private partial def paraQuot : ParserFn :=
    (nodeWithAntiquot "para" `Lean.Doc.Parser.Block.para (many1 (atomic { fn := inlineQuot }))).fn

  private partial def listItemQuot : ParserFn :=
    (nodeWithAntiquot "ListItem.item" `Lean.Doc.Parser.ListItem.item
      (listMarker >> many (atomic { fn := blockQuot }))).fn

  private partial def descItemQuot : ParserFn :=
    (nodeWithAntiquot "DescItem.item" `Lean.Doc.Parser.DescItem.item
      (atomOf ":" >> many (atomic { fn := inlineQuot }) >> many (atomic { fn := blockQuot }))).fn

  private partial def ulQuot : ParserFn :=
    (nodeWithAntiquot "ul" `Lean.Doc.Parser.Block.ul (many1 (atomic { fn := listItemQuot }))).fn

  private partial def olQuot : ParserFn :=
    (nodeWithAntiquot "ol" `Lean.Doc.Parser.Block.ol (many1 (atomic { fn := listItemQuot }))).fn

  private partial def dlQuot : ParserFn :=
    (nodeWithAntiquot "dl" `Lean.Doc.Parser.Block.dl (many1 (atomic { fn := descItemQuot }))).fn

  private partial def blockquoteQuot : ParserFn :=
    (nodeWithAntiquot "blockquote" `Lean.Doc.Parser.Block.blockquote
      (atomOf ">" >> many (atomic { fn := blockQuot }))).fn

  private partial def codeblockQuot : ParserFn :=
    (nodeWithAntiquot "codeblock" `Lean.Doc.Parser.Block.codeblock
      (codeBlockFence >> optional (Lean.Parser.ident >> many arg) >>
        versoCodeBlock >> codeBlockFence)).fn

  private partial def directiveQuot : ParserFn :=
    (nodeWithAntiquot "directive" `Lean.Doc.Parser.Block.directive
      (directiveDelimiter >> Lean.Parser.ident >> many arg >>
        many (atomic { fn := blockQuot }) >> directiveDelimiter)).fn

  private partial def headerQuot : ParserFn :=
    (nodeWithAntiquot "header" `Lean.Doc.Parser.Block.header
      (headerMarker >> many1 (atomic { fn := inlineQuot }))).fn

  private partial def linkRefQuot : ParserFn :=
    (nodeWithAntiquot "link_ref" `Lean.Doc.Parser.Block.link_ref
      (atomOf "[" >> versoRef >> atomOf "]:" >> versoLinkRefUrl)).fn

  private partial def footnoteRefQuot : ParserFn :=
    (nodeWithAntiquot "footnote_ref" `Lean.Doc.Parser.Block.footnote_ref
      (atomOf "[^" >> versoRef >> atomOf "]:" >> many (atomic { fn := inlineQuot }))).fn

  private partial def metadataQuot : ParserFn :=
    (nodeWithAntiquot "metadata_block" `Lean.Doc.Parser.Block.metadata_block
      (atomOf "%%%" >> metadataContentsLit >> atomOf "%%%")).fn

  private partial def commandQuot : ParserFn :=
    (nodeWithAntiquot "command" `Lean.Doc.Parser.Block.command
      (atomOf "{" >> Lean.Parser.ident >> many arg >> atomOf "}")).fn
end

namespace ListItem

@[inherit_doc Lean.Doc.Syntax.li, builtin_doc]
def item : Lean.Parser.Parser := { fn := listItemQuot }

end ListItem

namespace DescItem

@[inherit_doc Lean.Doc.Syntax.desc, builtin_doc]
def item : Lean.Parser.Parser := { fn := descItemQuot }

end DescItem

namespace Block

@[inherit_doc Lean.Doc.Syntax.para, builtin_doc]
def para : Lean.Parser.Parser := { fn := paraQuot }
@[inherit_doc Lean.Doc.Syntax.ul, builtin_doc]
def ul : Lean.Parser.Parser := { fn := ulQuot }
@[inherit_doc Lean.Doc.Syntax.ol, builtin_doc]
def ol : Lean.Parser.Parser := { fn := olQuot }
@[inherit_doc Lean.Doc.Syntax.dl, builtin_doc]
def dl : Lean.Parser.Parser := { fn := dlQuot }
@[inherit_doc Lean.Doc.Syntax.blockquote, builtin_doc]
def blockquote : Lean.Parser.Parser := { fn := blockquoteQuot }
@[inherit_doc Lean.Doc.Syntax.codeblock, builtin_doc]
def codeblock : Lean.Parser.Parser := { fn := codeblockQuot }
@[inherit_doc Lean.Doc.Syntax.directive, builtin_doc]
def directive : Lean.Parser.Parser := { fn := directiveQuot }
@[inherit_doc Lean.Doc.Syntax.header, builtin_doc]
def header : Lean.Parser.Parser := { fn := headerQuot }
@[inherit_doc Lean.Doc.Syntax.link_ref, builtin_doc]
def link_ref : Lean.Parser.Parser := { fn := linkRefQuot }
@[inherit_doc Lean.Doc.Syntax.footnote_ref, builtin_doc]
def footnote_ref : Lean.Parser.Parser := { fn := footnoteRefQuot }
@[inherit_doc Lean.Doc.Syntax.metadata_block, builtin_doc]
def metadata_block : Lean.Parser.Parser := { fn := metadataQuot }
@[inherit_doc Lean.Doc.Syntax.command, builtin_doc]
def command : Lean.Parser.Parser := { fn := commandQuot }

end Block

/-- Any block element. -/
def block : Lean.Parser.Parser := { fn := blockQuot }

open Lean.Parser in
/-- A Verso document, which is a sequence of blocks. -/
def document : Lean.Parser.Parser :=
  nodeWithAntiquot "document" decl_name% (many (atomic block))

end

end Lean.Doc.Parser


namespace Lean.Doc

public section

/--
A Verso document, which is a sequence of blocks.

Use `TSyntax.getVersoBlocks` to extract its contents.
-/
abbrev VersoDocument := TSyntax ``Parser.document

/--
A delimiter of a Verso element, such as the backticks around a code literal or the asterisks around
bold text. The markers that introduce a header, a list item, and mathematical notation are
delimiters too.

Each sits in a node of its own, so that a quotation can splice one in place of writing it out. Use
`TSyntax.getVersoDelimiter` to read its characters.
-/
abbrev VersoDelimiter :=
  TSyntax [``Parser.emphDelimiter, ``Parser.boldDelimiter,
    ``Parser.codeDelimiter, ``Parser.codeBlockFence,
    ``Parser.directiveDelimiter, ``Parser.headerMarker,
    ``Parser.listMarker, ``Parser.inlineMathMarker,
    ``Parser.displayMathMarker]

end

end Lean.Doc

namespace Lean.TSyntax

public section

open Lean.Doc

/--
Extracts the blocks of a Verso document.
-/
def getVersoBlocks (doc : VersoDocument) : TSyntaxArray ``Parser.block :=
  -- The repetition that reads the blocks groups them in a null node.
  doc.raw[0].getArgs.map (⟨·⟩)

/--
Returns the characters that make up a Verso delimiter.
-/
def getVersoDelimiter (delim : VersoDelimiter) : String :=
  delim.raw[0].getAtomVal

end

end Lean.TSyntax

namespace Lean.Doc

public section

/-- A document stands for the blocks it contains. -/
instance : Coe VersoDocument (TSyntaxArray ``Parser.block) where
  coe doc := doc.getVersoBlocks

end
