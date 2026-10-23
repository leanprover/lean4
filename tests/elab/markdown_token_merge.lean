import Lean.Server.FileWorker.SemanticHighlighting

/-!
Markup token unit tests.

These checks parse small Markdown snippets that exercise every combination of inline emphasis (none,
bold, italic, both) with every block context (plain, heading, blockquote, list), plus the markup
constructs whose tokens do not depend on the surrounding context (inline code, code blocks, URLs,
titles, and delimiters).
-/

open Lean Lsp Server.FileWorker

/--
Gets the token at byte offset `byteIdx` of `input` as its type name followed by its modifier names,
or `"<none>"` if no token includes the offset.
-/
def markupAt (input : String) (byteIdx : Nat) : String := Id.run do
  let text := FileMap.ofString input
  let toks := collectMarkdownTokens text 0 input.rawEndPos
  let tok? := toks.findSome? fun t => do
    guard <| t.range.start.byteIdx ≤ byteIdx && byteIdx < t.range.stop.byteIdx
    let type ← SemanticTokenType.names[t.type.toNat]?
    let modifiers := t.modifiers.filterMap fun m => SemanticTokenModifier.names[m.toNat]?
    return " ".intercalate (type :: modifiers)
  tok?.getD "<none>"

/-- Counts emitted tokens whose type name equals `typeName`. -/
def tokenCount (input : String) (typeName : String) : Nat := Id.run do
  let text := FileMap.ofString input
  let toks := collectMarkdownTokens text 0 input.rawEndPos
  let mut n := 0
  for t in toks do
    if SemanticTokenType.names[t.type.toNat]? == some typeName then
      n := n + 1
  return n

/-!
## Cross-product over (emphasis, block context)

Each line places an `x` content character inside the smallest snippet that produces the targeted
attribute combination. The block context selects the type, and the emphasis adds the `markupBold`
and `markupItalic` modifiers.
-/

-- plain × {none, bold, italic, both}
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "x" 0

/-- info: "markupDocText markupBold" -/
#guard_msgs in #eval markupAt "**x**" 2

/-- info: "markupDocText markupItalic" -/
#guard_msgs in #eval markupAt "*x*" 1

/-- info: "markupDocText markupBold markupItalic" -/
#guard_msgs in #eval markupAt "***x***" 3

-- heading × {none, bold, italic, both}
/-- info: "markupHeading" -/
#guard_msgs in #eval markupAt "# x" 2

/-- info: "markupHeading markupBold" -/
#guard_msgs in #eval markupAt "# **x**" 4

/-- info: "markupHeading markupItalic" -/
#guard_msgs in #eval markupAt "# *x*" 3

/-- info: "markupHeading markupBold markupItalic" -/
#guard_msgs in #eval markupAt "# ***x***" 5

-- blockquote × {none, bold, italic, both}
/-- info: "markupQuote" -/
#guard_msgs in #eval markupAt "> x" 2

/-- info: "markupQuote markupBold" -/
#guard_msgs in #eval markupAt "> **x**" 4

/-- info: "markupQuote markupItalic" -/
#guard_msgs in #eval markupAt "> *x*" 3

/-- info: "markupQuote markupBold markupItalic" -/
#guard_msgs in #eval markupAt "> ***x***" 5

-- list × {none, bold, italic, both}
/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* x" 2

/-- info: "markupList markupBold" -/
#guard_msgs in #eval markupAt "* **x**" 4

/-- info: "markupList markupItalic" -/
#guard_msgs in #eval markupAt "* *x*" 3

/-- info: "markupList markupBold markupItalic" -/
#guard_msgs in #eval markupAt "* ***x***" 5

/-!
## Delimiters

Every delimiter is a `keyword` token with the `markupSyntax` modifier.
-/

/-- info: ["keyword markupSyntax", "keyword markupSyntax", "keyword markupSyntax", "keyword markupSyntax"] -/
#guard_msgs in #eval ["**x**", "# x", "> x", "* x"].zipWith markupAt [0, 0, 0, 0]

/-!
## Code

Inline code and code blocks have fixed types without modifiers, regardless of surrounding
emphasis.
-/

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`x`" 1

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "**`x`**" 3

/-- info: "markupCodeBlock" -/
#guard_msgs in #eval markupAt "```\nx\n```" 4

-- Indented code blocks (4 leading spaces) get one `markupCodeBlock` token per
-- line, after the four columns of indentation.
/-- info: "markupCodeBlock" -/
#guard_msgs in #eval markupAt "    indented\n    code block\n" 4

/-- info: "<none>" -/
#guard_msgs in #eval markupAt "    indented\n    code block\n" 3

/-- info: 2 -/
#guard_msgs in #eval tokenCount "    indented\n    code block\n" "markupCodeBlock"

-- HTML blocks get one `markupCodeBlock` token per line; their content is not parsed as Markdown.
/-- info: "markupCodeBlock" -/
#guard_msgs in #eval markupAt "<div>\n*x*\n</div>\n" 7

/-- info: 3 -/
#guard_msgs in #eval tokenCount "<div>\n*x*\n</div>\n" "markupCodeBlock"

-- Inline code that crosses a line break: each line of the content gets its
-- own `markupInlineCode` token (LSP semantic tokens are per-line), and the
-- delimiters remain delimiters.
/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`a\nb`" 1

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`a\nb`" 3

/-!
## Image alt content

Per CommonMark §6.4, an image description has inline elements as its
contents (with the same rules as link text, plus that links are explicitly
permitted). The highlighter visits alt content recursively, so emphasis,
inline code, and links inside alt text receive their normal token types.
-/

-- Plain alt text gets the ambient context (here, plain).
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "![x](http://e.com)" 2

-- Bold inside alt: the inner content character has the modifier.
/-- info: "markupDocText markupBold" -/
#guard_msgs in #eval markupAt "![**x**](http://e.com)" 4

-- Inline code inside alt is still `markupInlineCode`.
/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "![`x`](http://e.com)" 3

-- Autolink inside alt: the URL is `markupUrl`.
/-- info: "markupUrl" -/
#guard_msgs in #eval markupAt "![<https://e.com>](http://e.com)" 3

/-!
## Order independence

The two snippets nest bold and italic in opposite orders. The inner content
character must receive the same modifiers in both arrangements; otherwise
attribute accumulation depends on traversal order.
-/

/-- info: "markupDocText markupBold markupItalic" -/
#guard_msgs in #eval markupAt "**a *x* a**" 5

/-- info: "markupDocText markupBold markupItalic" -/
#guard_msgs in #eval markupAt "*a **x** a*" 5

/-- info: "markupHeading markupBold markupItalic" -/
#guard_msgs in #eval markupAt "# **a *x* a**" 7

/-- info: "markupHeading markupBold markupItalic" -/
#guard_msgs in #eval markupAt "# *a **x** a*" 7

/-- info: "markupQuote markupBold markupItalic" -/
#guard_msgs in #eval markupAt "> **a *x* a**" 7

/-- info: "markupQuote markupBold markupItalic" -/
#guard_msgs in #eval markupAt "> *a **x** a*" 7

/-- info: "markupList markupBold markupItalic" -/
#guard_msgs in #eval markupAt "* **a *x* a**" 7

/-- info: "markupList markupBold markupItalic" -/
#guard_msgs in #eval markupAt "* *a **x** a*" 7

/-!
## Soft breaks do not produce multi-line tokens

The inline parser emits a one-byte `.softBreak` element for each `\n`
between paragraph lines so downstream renderers can reproduce the line
ending. The semantic-token emitter must not turn that element into an LSP
token, since VS Code does not support multi-line semantic tokens.
-/

-- Soft break between two paragraph lines: byte 5 is the `\n`.
/-- info: "<none>" -/
#guard_msgs in #eval markupAt "hello\nworld" 5

-- Soft break inside a heading.
/-- info: "<none>" -/
#guard_msgs in #eval markupAt "# a *cross\nline* b" 10

-- Surrounding line content still receives its expected types.
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "hello\nworld" 0

/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "hello\nworld" 6

/-!
## Multi-line link reference definitions

A ref-def label may span newlines (CommonMark §4.7) and a title may sit
on the line that follows the URL. Both are split at line boundaries so each
emitted token stays on a single line.
-/

-- Two-line label: one `markupCrossReference` token per source line.
/-- info: 2 -/
#guard_msgs in #eval tokenCount "[foo\nbar]: https://e.com\n" "markupCrossReference"

-- Two-line title: one `string` token per line.
/-- info: 2 -/
#guard_msgs in #eval tokenCount "[a]: https://e.com \"title\nspans lines\"\n" "string"

/-!
## Ref defs inside blockquotes

`postProcessRefDefs` descends into blockquote and list children, so a ref
def inside a blockquote still produces a `markupCrossReference` token on
its label.
-/

/-- info: "markupCrossReference" -/
#guard_msgs in #eval markupAt "> [foo]: https://e.com\n" 3

/-!
## ATX heading guards

Seven or more `#` characters are not a valid ATX heading (CommonMark
§4.2 caps the level at six). The line falls through to a paragraph and
its content receives the plain `markupDocText` type.
-/

/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "####### x" 8

-- Six hashes is still a heading.
/-- info: "markupHeading" -/
#guard_msgs in #eval markupAt "###### x" 7

/-!
## Nested lists with mixed bullet kinds

Different bullet characters at different nesting levels form distinct
sibling-incompatible lists. The inner list's content still receives the
`markupList` type.
-/

/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* outer\n  - inner" 12

/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* outer\n  + inner" 12

/-!
## Link titles

A title's delimiters are markup syntax like the brackets around the link text, and its text is a
string, both for inline targets and for link reference definitions.
-/

/-- info: ["keyword markupSyntax", "string", "keyword markupSyntax"] -/
#guard_msgs in #eval ["[a](/u \"t\")", "[a](/u \"t\")", "[a](/u \"t\")"].zipWith markupAt [7, 8, 9]

/-- info: ["keyword markupSyntax", "string", "keyword markupSyntax"] -/
#guard_msgs in #eval ["[r]: /u (t)", "[r]: /u (t)", "[r]: /u (t)"].zipWith markupAt [8, 9, 10]

/-!
## Hard breaks and escapes

The backslash or the trailing spaces that make a line ending a hard break are markup syntax, as is
the backslash of an escape. The escaped character is text.
-/

/-- info: ["keyword markupSyntax", "keyword markupSyntax"] -/
#guard_msgs in #eval ["a\\\nb", "a  \nb"].zipWith markupAt [1, 1]

/-- info: ["keyword markupSyntax", "markupDocText"] -/
#guard_msgs in #eval ["\\*x", "\\*x"].zipWith markupAt [0, 1]

/-!
## Content that continues onto the next line of a container

Inline code, a link title, or a reference label that continues onto the next line of a blockquote gets
one token per line, and the blockquote marker on the second line stays a delimiter.
-/

/-- info: ["keyword markupSyntax", "<none>", "markupInlineCode"] -/
#guard_msgs in #eval ["> `a\n> b`", "> `a\n> b`", "> `a\n> b`"].zipWith markupAt [5, 6, 7]

/-- info: ["keyword markupSyntax", "string"] -/
#guard_msgs in #eval ["> [x](/u \"t\n> u\")", "> [x](/u \"t\n> u\")"].zipWith markupAt [12, 14]

/-- info: ["keyword markupSyntax", "markupCrossReference"] -/
#guard_msgs in #eval ["> [foo\n> bar]: /u", "> [foo\n> bar]: /u"].zipWith markupAt [7, 9]

/-- info: ["markupCrossReference", "markupCrossReference"] -/
#guard_msgs in #eval ["[t][a\nb]\n\n[a b]: /u", "[t][a\nb]\n\n[a b]: /u"].zipWith markupAt [4, 6]

/-!
## Raw HTML

Inline HTML is inline code, one token per line.
-/

/-- info: ["markupInlineCode", "markupDocText", "markupInlineCode"] -/
#guard_msgs in #eval ["a <b>c</b>", "a <b>c</b>", "a <b>c</b>"].zipWith markupAt [2, 5, 7]

/-!
## Indented documents

With a nonzero indent, the indentation of the document as a whole is skipped, so a continuation line
that is indented by it is text and only lines that are indented four columns past it are code.
-/

def markupAtIndented (input : String) (indent byteIdx : Nat) : String := Id.run do
  let text := FileMap.ofString input
  let toks := collectMarkdownTokens text 0 input.rawEndPos indent
  let tok? := toks.findSome? fun t => do
    guard <| t.range.start.byteIdx ≤ byteIdx && byteIdx < t.range.stop.byteIdx
    SemanticTokenType.names[t.type.toNat]?
  tok?.getD "<none>"

/-- info: ["markupDocText", "markupCodeBlock", "markupCodeBlock"] -/
#guard_msgs in #eval
  ["  a\n\n    b", "  a\n\n      c", "a\n\n    b"].zipWith (fun s (i, p) => markupAtIndented s i p) [(2, 9), (2, 11), (0, 7)]

-- A fenced code block that is indented inside an indented document: the code token starts after the
-- document's two columns of indentation and the fence's two, so byte 11 (the last of those four
-- spaces) is untokenized and byte 12 (the first of the line's own two spaces) is code.
/-- info: ["<none>", "markupCodeBlock"] -/
#guard_msgs in #eval
  ["    ```\n      x\n    ```\n", "    ```\n      x\n    ```\n"].zipWith (fun s (i, p) => markupAtIndented s i p) [(2, 11), (2, 12)]

/-!
## Bracketed destinations

The angle brackets around a destination are markup syntax, and only the URL between them is a URL,
both for inline targets and for link reference definitions.
-/

/-- info: ["keyword markupSyntax", "markupUrl", "keyword markupSyntax"] -/
#guard_msgs in #eval ["[a](<u>)", "[a](<u>)", "[a](<u>)"].zipWith markupAt [4, 5, 6]

/-- info: ["keyword markupSyntax", "markupUrl", "keyword markupSyntax"] -/
#guard_msgs in #eval ["[r]: <u>", "[r]: <u>", "[r]: <u>"].zipWith markupAt [5, 6, 7]
