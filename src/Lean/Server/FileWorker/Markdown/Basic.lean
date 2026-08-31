/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Hashable
public import Std.Data.HashMap
public import Lean.Syntax

public section

namespace Lean.Server.FileWorker.Markdown

/-- The marker character of a bullet list. -/
inductive BulletKind where
  /-- A `*`-marked bullet list. -/
  | star
  /-- A `-`-marked bullet list. -/
  | hyphen
  /-- A `+`-marked bullet list. -/
  | plus
deriving Repr, BEq, Hashable

/-- The terminating delimiter of an ordered-list marker. -/
inductive OrderedDelim where
  /-- A `.` delimiter, as in `1.` -/
  | dot
  /-- A `)` delimiter, as in `1)` -/
  | rparen
deriving Repr, BEq, Hashable

/--
The kind of a list. All items in a list must share the same kind: an unordered list cannot mix `*`
with `-`, and an ordered list cannot mix `1.` with `1)`.
-/
inductive ListKind where
  /-- A bullet list with the given marker character. -/
  | bullet (kind : BulletKind)
  /--
  An ordered list. `start` is the value of the first item; `delim` is the
  punctuation following the digits.
  -/
  | ordered (start : Nat) (delim : OrderedDelim)
deriving Repr, BEq, Hashable

/-- The fence character used by a fenced code block. -/
inductive FenceChar where
  /-- A backtick (`` ` ``) fence. The info string may not contain backticks. -/
  | backtick
  /-- A tilde (`~`) fence. -/
  | tilde
deriving Repr, BEq, Hashable, Inhabited

namespace FenceChar

def ofChar? : Char → Option FenceChar
  | '`' => some .backtick
  | '~' => some .tilde
  | _ => none

def toChar : FenceChar → Char
  | .backtick => '`'
  | .tilde => '~'

end FenceChar

/-- Information attached to a fenced code block at its opening fence. -/
structure FenceInfo where
  /-- The fence character: `` ` `` or `~`. -/
  fenceChar : FenceChar
  /--
  The length of the opening fence run (always 3 or more). The closing fence must be at least this
  long and use the same character.
  -/
  fenceLen : Nat
  /--
  Indentation in spaces of the opening fence's first character. Up to this many leading spaces are
  stripped from each content line before it is treated as code.
  -/
  openIndent : Nat
  /-- The info string range, if it exists. This is usually a language tag. -/
  infoString? : Option Syntax.Range
deriving Repr, BEq, Hashable, Inhabited

/--
The source ranges of a link reference definition's structural parts. The
label is the bracket interior (excluding the brackets themselves); the
URL is the destination (including any `<>` wrappers if used); `title?`
is the optional title's interior (excluding the surrounding quote/paren
delimiters).

For multi-line reference definitions, ranges may span newlines.
-/
structure RefDef where
  /-- The opening `[` of the label. -/
  openBracket : Syntax.Range
  /-- The label's interior, between the brackets (un-normalized). -/
  label : Syntax.Range
  /-- The closing `]` of the label. -/
  closeBracket : Syntax.Range
  /-- The `:` separating the label from the destination. -/
  colon : Syntax.Range
  /--
  The destination's source range. Includes the `<>` wrappers if the destination uses bracketed form.
  -/
  url : Syntax.Range
  /--
  The optional title's interior, excluding its surrounding delimiters (`"…"`, `'…'`, or `(…)`).
  -/
  title? : Option Syntax.Range
deriving Repr, Inhabited

/--
A fully parsed block-level subtree.

The type parameter `α` is the kind of inline-bearing content each block holds:

- After the first pass, in which the type and extent of all blocks have been determined but the
  inlines have not yet been parsed, `α := Syntax.Range`. Each paragraph or heading line is one such
  range.
- After the second pass, which parses the inline elements, `α := Array Inline`. The resulting
  `lines` array of a `paragraph` or `setextHeading` always contains exactly one element: the inline
  element syntax tree that represents the whole paragraph.

Verbatim blocks (`fencedCode`, `indentedCode`) and structural blocks (`linkRefDef`) do not carry
`α`-typed content; they only ever hold raw source ranges, regardless of which pass has run.
-/
inductive Block (α : Type) where
  /--
  A paragraph: a sequence of consecutive non-blank lines that did not open
  any other leaf.
  -/
  | paragraph (lines : Array α)
  /--
  An ATX heading (the usual kind). `hashes` covers the opening run of `#` characters,
  `closeHashes?` covers an optional closing run.
  -/
  | atxHeading (hashes : Syntax.Range) (content : α) (closeHashes? : Option Syntax.Range)
  /--
  A setext heading (CommonMark §4.3): one or more lines of paragraph text followed by an underline
  (`===` for level 1, `---` for level 2). `lines` is the content of the preceding paragraph, and
  `underline` covers the underline itself.
  -/
  | setextHeading (level : Nat) (lines : Array α) (underline : Syntax.Range)
  /--
  A fenced code block. `openFence`/`closeFence?` cover the fences runs themselves. The closing fence
  is optional because an unterminated fenced code block spans the rest of the input.
  -/
  | fencedCode (info : FenceInfo)
    (openFence : Syntax.Range) (closeFence? : Option Syntax.Range)
    (lines : Array Syntax.Range)
  /--
  An indented code block: a sequence of lines indented four or more columns. Each element is a
  pair of the line's source range (covering the whole source line, including the indent that the
  block consumed) and its processed content. In the processed content, the leading 4 cols of indent
  (relative to the parent container) have been stripped, with any partial tabs materialized as the
  appropriate number of spaces per CommonMark §2.2.
  -/
  | indentedCode (lines : Array (Syntax.Range × String))
  /--
  A blockquote container. `markers` records the position of every `>` marker located during parsing,
  in source order and `children` holds the contained blocks.
  -/
  | blockquote (markers : Array Syntax.Range) (children : Array (Block α))
  /--
  A list container. All `items` are `listItem` blocks. `tight` reflects CommonMark's tight/loose
  distinction (§5.3): a tight list has no blank lines between its items or between blocks within an
  item. HTML rendering unwraps `<p>` from a tight list item's direct paragraph children.
  -/
  | list (kind : ListKind) (tight : Bool) (items : Array (Block α))
  /--
  A list item. `marker` is the bullet or ordered-marker range emitted as a delimiter token, and
  `children` are the blocks contained inside the item.
  -/
  | listItem (marker : Syntax.Range) (children : Array (Block α))
  /--
  A link reference definition: `[label]: destination "title"` (the title is optional).
  -/
  | linkRefDef (m : RefDef)
  /--
  A thematic break (`***`, `---`, or `___`, optionally with interior spaces or
  tabs). The line range covers the entire source line that produced the break.
  -/
  | thematicBreak (line : Syntax.Range)
deriving Inhabited

namespace ListKind

/--
Whether two list kinds belong to the same list (that is, they have matching marker styles).

The starting number of an ordered list is irrelevant: `1.` and `5.` are the same list kind. Bullets
must use the exact same character, and ordered lists must use the same delimiter.
-/
def sameKind : ListKind → ListKind → Bool
  | .bullet a, .bullet b => a == b
  | .ordered _ d1, .ordered _ d2 => d1 == d2
  | _, _ => false

end ListKind

/--
The surface form of a reference-style link or image.
-/
inductive ReferenceLinkForm where
  /--
  Full form `[text][label]` — the second brackets carry an explicit
  label, distinct from the link's text. `openBracket`/`closeBracket`
  cover the second bracket pair; `label` is the bracket interior.
  -/
  | full (openBracket : Syntax.Range) (label : Syntax.Range) (closeBracket : Syntax.Range)
  /--
  Collapsed form `[text][]`. The second brackets are empty, and the link's text serves as the label.
  `openBracket`/`closeBracket` cover the empty second bracket pair.
  -/
  | collapsed (openBracket : Syntax.Range) (closeBracket : Syntax.Range)
  /--
  Shortcut form `[label]`. There are no second brackets and the link's text serves as the label.
  -/
  | shortcut
deriving Repr, Inhabited

/-- The destination of a link or image. -/
inductive LinkTarget where
  /--
  An inline target `(url)` or `(url "title")`. The title (if present) excludes its surrounding
  delimiter characters.
  -/
  | inline (openParen : Syntax.Range) (url : Syntax.Range) (closeParen : Syntax.Range)
    (title? : Option Syntax.Range := none)
  /--
  A reference target.

  The reference table has been consulted at parse time, so `url` and `title?` are already the
  resolved destination/title from the matching link reference definition. In Markdown, unresolvable
  references never produce a `link`/`image`; instead, the surrounding bracket characters fall
  through to plain text.
  -/
  | reference (url : String) (title? : Option String) (form : ReferenceLinkForm)
deriving Repr, Inhabited

/-- A parsed inline element. -/
inductive Inline where
  /-- Plain text. -/
  | text (range : Syntax.Range)
  /-- Inline code span. The content is verbatim source. -/
  | code (openTicks : Syntax.Range) (content : Syntax.Range) (closeTicks : Syntax.Range)
  /-- Italic emphasis. -/
  | italic (openDelim : Syntax.Range) (content : Array Inline) (closeDelim : Syntax.Range)
  /-- Bold/strong emphasis. -/
  | bold (openDelim : Syntax.Range) (content : Array Inline) (closeDelim : Syntax.Range)
  /-- Inline or reference link. The text is recursively parsed. -/
  | link (openBracket : Syntax.Range) (text : Array Inline) (closeBracket : Syntax.Range)
    (target : LinkTarget)
  /--
  An image. The alt content is recursively parsed as inline content (CommonMark §6.4); HTML
  rendering should flatten it to plain text for the `alt` attribute.
  -/
  | image (bang : Syntax.Range) (openBracket : Syntax.Range) (alt : Array Inline)
    (closeBracket : Syntax.Range) (target : LinkTarget)
  /--
  A hard line break. These are produced by a backslash immediately before a line ending or by two or
  more trailing spaces before a line ending (CommonMark §6.7). The range covers the trigger
  characters (e.g. the `\` for backslash form).
  -/
  | hardBreak (range : Syntax.Range)
  /--
  An autolink: `<https://...>` or `<scheme:...>` for URI form, or `<user@domain>` for email form
  (CommonMark §6.5). The URL between the angle brackets is verbatim — no backslash-escape, entity,
  or other markdown processing applies inside. `isEmail` distinguishes the email form, whose href
  gets a `mailto:` prefix when rendered to HTML.
  -/
  | autolink (openAngle : Syntax.Range) (url : Syntax.Range) (closeAngle : Syntax.Range)
    (isEmail : Bool)
deriving Inhabited

/--
A normalized link label.

According to the CommonMark spec §4.7, link labels are normalized as follows:
* They are case-folded (though this implementation does not implement full Unicode case folding)
* Internal whitespace is collapsed to a single space
* Leading and trailing whitespace are removed

The constructor is private. Build values via `normalizeLabel`.
-/
structure LinkLabel where
  private mk ::
  /-- The normalized label string (see `normalizeLabel`). -/
  name : String
deriving BEq, Hashable, Repr

/--
Normalizes a CommonMark link label (§4.7):
 * Each character is ASCII-lowercased (with `Char.toLower`).
 * Internal whitespace runs become single spaces.
 * Leading and trailing whitespace is removed.

While CommonMark specifies Unicode case folding, this implementation case-folds only ASCII English
letters.
-/
public def normalizeLabel (s : String) : LinkLabel := Id.run do
  let mut out := ""
  let mut sawWs := false  -- whether we've seen whitespace since the last non-ws
  let mut sawNonWs := false  -- whether we've emitted any non-ws char yet
  for c in s do
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then
      sawWs := true
    else
      if sawNonWs && sawWs then out := out.push ' '
      out := out.push c.toLower
      sawWs := false
      sawNonWs := true
  return ⟨out⟩

/--
The destination of a link reference definition: the URL plus optional title.
-/
structure RefTarget where
  /-- The destination URL with any `<>` wrappers stripped. -/
  url : String
  /-- The optional title, with its surrounding delimiters stripped. -/
  title? : Option String
deriving Repr, Inhabited

/--
A reference table built from a document's link reference definitions.

During inline parsing, these are used to recognize valid references.
-/
abbrev RefTable := Std.HashMap LinkLabel RefTarget
