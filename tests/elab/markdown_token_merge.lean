import Lean.Server.FileWorker.SemanticHighlighting

/-!
Markup token cross-product unit tests.

These checks parse small Markdown snippets that exercise every combination of
inline emphasis (none, bold, italic, both) with every block context (plain,
heading, blockquote, list), plus the non-composing overrides (inline code,
fenced code block, image alt).
-/

open Lean Lsp Server.FileWorker

/-- Gets the token type at byte offset `byteIdx` of `input`, or `"<none>"` if no token covers it. -/
def markupAt (input : String) (byteIdx : Nat) : String := Id.run do
  let text := FileMap.ofString input
  let toks := collectMarkdownTokens text 0 input.rawEndPos
  let tok? := toks.findSome? fun t => do
    let r ← t.stx.getRange?
    guard <| r.start.byteIdx ≤ byteIdx && byteIdx < r.stop.byteIdx
    SemanticTokenType.names[t.type.toNat]?
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

/-! ## Cross-product over (emphasis, block context)

Each line places an `x` content character inside the smallest snippet that
produces the targeted attribute combination. The expected token name follows
the `markup{Bold?}{Italic?}{Block}` convention.
-/

-- plain × {none, bold, italic, both}
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "x" 0

/-- info: "markupBold" -/
#guard_msgs in #eval markupAt "**x**" 2

/-- info: "markupItalic" -/
#guard_msgs in #eval markupAt "*x*" 1

/-- info: "markupBoldItalic" -/
#guard_msgs in #eval markupAt "***x***" 3

-- heading × {none, bold, italic, both}
/-- info: "markupHeading" -/
#guard_msgs in #eval markupAt "# x" 2

/-- info: "markupBoldHeading" -/
#guard_msgs in #eval markupAt "# **x**" 4

/-- info: "markupItalicHeading" -/
#guard_msgs in #eval markupAt "# *x*" 3

/-- info: "markupBoldItalicHeading" -/
#guard_msgs in #eval markupAt "# ***x***" 5

-- blockquote × {none, bold, italic, both}
/-- info: "markupQuote" -/
#guard_msgs in #eval markupAt "> x" 2

/-- info: "markupBoldQuote" -/
#guard_msgs in #eval markupAt "> **x**" 4

/-- info: "markupItalicQuote" -/
#guard_msgs in #eval markupAt "> *x*" 3

/-- info: "markupBoldItalicQuote" -/
#guard_msgs in #eval markupAt "> ***x***" 5

-- list × {none, bold, italic, both}
/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* x" 2

/-- info: "markupBoldList" -/
#guard_msgs in #eval markupAt "* **x**" 4

/-- info: "markupItalicList" -/
#guard_msgs in #eval markupAt "* *x*" 3

/-- info: "markupBoldItalicList" -/
#guard_msgs in #eval markupAt "* ***x***" 5

/-! ## Non-composing overrides

Inline code and fenced code blocks are fixed regardless of surrounding
emphasis: their `markup*` type does not stack with the active attributes.
-/

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`x`" 1

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "**`x`**" 3

/-- info: "markupCodeBlock" -/
#guard_msgs in #eval markupAt "```\nx\n```" 4

-- Indented code blocks (4 leading spaces) get one `markupCodeBlock` token per
-- line, covering the whole source line including the indent.
/-- info: "markupCodeBlock" -/
#guard_msgs in #eval markupAt "    indented\n    code block\n" 4

/-- info: 2 -/
#guard_msgs in #eval tokenCount "    indented\n    code block\n" "markupCodeBlock"

-- A code span that crosses a line break: each line of the content gets its
-- own `markupInlineCode` token (LSP semantic tokens are per-line), and the
-- delimiters remain `keyword`.
/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`a\nb`" 1

/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "`a\nb`" 3

/-! ## Image alt content

Per CommonMark §6.5, an image description has inline elements as its
contents (with the same rules as link text, plus that links are explicitly
permitted). The highlighter walks alt content recursively, so emphasis,
inline code, and links inside alt text receive their normal token types.
-/

-- Plain alt text gets the ambient context (here, plain).
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "![x](http://e.com)" 2

-- Bold inside alt: the inner content character is `markupBold`.
/-- info: "markupBold" -/
#guard_msgs in #eval markupAt "![**x**](http://e.com)" 4

-- Inline code inside alt is still `markupInlineCode`.
/-- info: "markupInlineCode" -/
#guard_msgs in #eval markupAt "![`x`](http://e.com)" 3

-- Autolink inside alt: the URL is `markupUrl`.
/-- info: "markupUrl" -/
#guard_msgs in #eval markupAt "![<https://e.com>](http://e.com)" 3

/-! ## Order independence

The two snippets nest bold and italic in opposite orders. The inner content
character must receive the same `markupBoldItalic*` type in both
arrangements; otherwise attribute accumulation depends on walk direction.
-/

/-- info: "markupBoldItalic" -/
#guard_msgs in #eval markupAt "**a *x* a**" 5

/-- info: "markupBoldItalic" -/
#guard_msgs in #eval markupAt "*a **x** a*" 5

/-- info: "markupBoldItalicHeading" -/
#guard_msgs in #eval markupAt "# **a *x* a**" 7

/-- info: "markupBoldItalicHeading" -/
#guard_msgs in #eval markupAt "# *a **x** a*" 7

/-- info: "markupBoldItalicQuote" -/
#guard_msgs in #eval markupAt "> **a *x* a**" 7

/-- info: "markupBoldItalicQuote" -/
#guard_msgs in #eval markupAt "> *a **x** a*" 7

/-- info: "markupBoldItalicList" -/
#guard_msgs in #eval markupAt "* **a *x* a**" 7

/-- info: "markupBoldItalicList" -/
#guard_msgs in #eval markupAt "* *a **x** a*" 7

/-! ## Soft breaks do not produce multi-line tokens

The inline parser emits a one-byte `.text` element covering each `\n`
between paragraph lines so downstream renderers can reproduce the line
ending. The semantic-token emitter must not turn that element into an LSP
token, since VS Code does not support multi-line semantic tokens.
-/

-- Soft break between two paragraph lines: byte 5 is the `\n`.
/-- info: "<none>" -/
#guard_msgs in #eval markupAt "hello\nworld" 5

-- Soft break inside a heading inline run.
/-- info: "<none>" -/
#guard_msgs in #eval markupAt "# a *cross\nline* b" 10

-- Surrounding line content still receives its expected types.
/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "hello\nworld" 0

/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "hello\nworld" 6

/-! ## Multi-line link reference definitions

A ref-def label may span newlines (CommonMark §4.7) and a title may sit
on the line following the URL. Both are split at line boundaries so each
emitted token stays on a single line.
-/

-- Two-line label: one `markupCrossReference` token per source line.
/-- info: 2 -/
#guard_msgs in #eval tokenCount "[foo\nbar]: https://e.com\n" "markupCrossReference"

-- Two-line title: one `string` token per line.
/-- info: 2 -/
#guard_msgs in #eval tokenCount "[a]: https://e.com \"title\nspans lines\"\n" "string"

/-! ## Ref defs inside blockquotes

`postProcessRefDefs` walks into blockquote and list children, so a ref
def inside a blockquote still produces a `markupCrossReference` token on
its label.
-/

/-- info: "markupCrossReference" -/
#guard_msgs in #eval markupAt "> [foo]: https://e.com\n" 3

/-! ## ATX heading guards

Seven or more `#` characters are not a valid ATX heading (CommonMark
§4.2 caps the level at six). The line falls through to a paragraph and
its content receives the plain `markupDocText` type.
-/

/-- info: "markupDocText" -/
#guard_msgs in #eval markupAt "####### x" 8

-- Six hashes is still a heading.
/-- info: "markupHeading" -/
#guard_msgs in #eval markupAt "###### x" 7

/-! ## Nested lists with mixed bullet kinds

Different bullet characters at different nesting levels form distinct
sibling-incompatible lists. The inner list's content still receives the
`markupList` type.
-/

/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* outer\n  - inner" 12

/-- info: "markupList" -/
#guard_msgs in #eval markupAt "* outer\n  + inner" 12
