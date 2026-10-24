/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.Data.Hashable
public import Std.Data.HashMap
public import Init.Data.String.Subslice
public import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.Data.String.Iterate
import Init.While
import Init.Data.String.TakeDrop
import Lean.Data.Markdown.Unicode.CaseFolding
import Lean.Data.Markdown.Text
public import Init.Data.String.FindPos

namespace Lean.Markdown


/-- The marker character of a bullet list. -/
public inductive BulletKind where
  /-- A `*`-marked bullet list. -/
  | star
  /-- A `-`-marked bullet list. -/
  | hyphen
  /-- A `+`-marked bullet list. -/
  | plus
deriving Repr, BEq, Hashable

/-- The terminating delimiter of an ordered-list marker. -/
public inductive OrderedDelim where
  /-- A `.` delimiter, as in `1.` -/
  | dot
  /-- A `)` delimiter, as in `1)` -/
  | rparen
deriving Repr, BEq, Hashable

/--
The kind of a list. All items in a list must share the same kind: an unordered list cannot mix `*`
with `-`, and an ordered list cannot mix `1.` with `1)`.
-/
public inductive ListKind where
  /-- A bullet list with the given marker character. -/
  | bullet (kind : BulletKind)
  /--
  An ordered list. `start` is the value of the first item; `delim` is the
  punctuation that follows the digits.
  -/
  | ordered (start : Nat) (delim : OrderedDelim)
deriving Repr, BEq, Hashable

/-- The fence character that a fenced code block uses. -/
public inductive FenceChar where
  /-- A backtick (`` ` ``) fence. The info string may not contain backticks. -/
  | backtick
  /-- A tilde (`~`) fence. -/
  | tilde
deriving Repr, BEq, Hashable, Inhabited

namespace FenceChar

public def ofChar? : Char → Option FenceChar
  | '`' => some .backtick
  | '~' => some .tilde
  | _ => none

public def toChar : FenceChar → Char
  | .backtick => '`'
  | .tilde => '~'

end FenceChar

/-- Information that is attached to a fenced code block at its opening fence. -/
public structure FenceInfo (s : String.Slice) where
  /-- The fence character: `` ` `` or `~`. -/
  fenceChar : FenceChar
  /--
  The length of the opening fence (always 3 or more). The closing fence must be at least this long
  and use the same character.
  -/
  fenceLen : Nat
  /--
  Indentation in spaces of the opening fence's first character. The content lines exclude up to
  this many leading spaces.
  -/
  openIndent : Nat
  /-- The info string, if there is one. This is usually a language tag. -/
  infoString? : Option s.Subslice
deriving Inhabited

/--
A line of a code block or HTML block, after the prefixes of the enclosing containers and the block's
own indentation.

A tab spans the columns up to the next tab stop (CommonMark §2.2), so the indentation may end
partway through a tab. Such a tab is not part of `source`, and its columns after the indentation
are `leadingSpaces`.
-/
public structure VerbatimLine (s : String.Slice) where
  /-- The line's source, without its line ending. -/
  source : s.Subslice
  /-- The number of columns of a tab that the indentation ends partway through. -/
  leadingSpaces : Nat := 0
deriving Inhabited

/-- The line's text: `leadingSpaces` spaces followed by the source. -/
public def VerbatimLine.text {s : String.Slice} (line : VerbatimLine s) : String :=
  "".pushn ' ' line.leadingSpaces ++ line.source.copy

/--
The text of a construct that may span source lines: one subslice per line, in source order, with at
least one line. The subslices exclude the line endings and the prefixes of enclosing containers.
-/
public structure Lines (s : String.Slice) where
  /-- The subslices, one per source line, in source order. -/
  toArray : Array s.Subslice
  /-- There is at least one line. -/
  nonempty : 0 < toArray.size

namespace Lines

variable {s : String.Slice}

/-- A single line. -/
public def singleton (line : s.Subslice) : Lines s := ⟨#[line], by simp⟩

/-- Appends a line. -/
public def push (lines : Lines s) (line : s.Subslice) : Lines s :=
  ⟨lines.toArray.push line, by simp⟩

/-- The first line. -/
public def first (lines : Lines s) : s.Subslice := lines.toArray[0]'lines.nonempty

/-- The last line. -/
public def last (lines : Lines s) : s.Subslice := lines.toArray.back lines.nonempty

/-- The text of each line, as a string. -/
public def copy (lines : Lines s) : Array String := lines.toArray.map (·.copy)

/-- The text of the lines, joined by `sep`. -/
public def text (lines : Lines s) (sep : String := "\n") : String :=
  sep.intercalate lines.copy.toList

public instance : Inhabited (Lines s) := ⟨singleton default⟩

end Lines

/--
The title of a link, image, or link reference definition: `"…"`, `'…'`, or `(…)`.
-/
public structure LinkTitle (s : String.Slice) where
  /-- The opening `"`, `'`, or `(`. -/
  opener : s.Subslice
  /-- The text between the delimiters. -/
  content : Lines s
  /-- The closing `"`, `'`, or `)`. -/
  closer : s.Subslice
deriving Inhabited

/-- The title that `t` denotes, with backslash escapes and character references decoded. -/
public def LinkTitle.text {s : String.Slice} (t : LinkTitle s) : String :=
  decodeText t.content.text

/--
The destination of a link, image, or link reference definition: a URL, optionally in angle brackets.
-/
public structure LinkDestination (s : String.Slice) where
  /-- The `<` and `>` around the URL, if the destination is bracketed. -/
  angles? : Option (s.Subslice × s.Subslice)
  /-- The URL as written, excluding any angle brackets. -/
  url : s.Subslice
deriving Inhabited

/-- The URL that `d` denotes, with backslash escapes and character references decoded. -/
public def LinkDestination.text {s : String.Slice} (d : LinkDestination s) : String :=
  decodeText d.url.copy

/--
The structural parts of a link reference definition. The label is the bracket interior (excluding
the brackets themselves).
-/
public structure RefDef (s : String.Slice) where
  /-- The opening `[` of the label. -/
  openBracket : s.Subslice
  /-- The label's interior, between the brackets (un-normalized). -/
  label : Lines s
  /-- The closing `]` of the label. -/
  closeBracket : s.Subslice
  /-- The `:` that separates the label from the destination. -/
  colon : s.Subslice
  /-- The destination. -/
  destination : LinkDestination s
  /-- The optional title. -/
  title? : Option (LinkTitle s)
deriving Inhabited

/--
A block of the source string `s` after the first pass, which determines the type and extent of every
block but does not parse inline content. Paragraphs and setext headings consist of their source
lines, with container prefixes such as `>` removed.
-/
public inductive Block.Raw (s : String.Slice) where
  /--
  A paragraph: a sequence of consecutive non-blank lines that did not open any other leaf.
  -/
  | paragraph (lines : Array s.Subslice)
  /--
  An ATX heading (the usual kind). `level` is the number of opening `#` characters, `hashes` is that
  opening sequence, and `closeHashes?` an optional closing sequence.
  -/
  | atxHeading (level : Nat) (hashes : s.Subslice) (content : s.Subslice)
      (closeHashes? : Option s.Subslice)
  /--
  A setext heading (CommonMark §4.3): one or more lines of paragraph text that are followed by an
  `underline` (`===` for level 1, `---` for level 2).
  -/
  | setextHeading (level : Nat) (lines : Array s.Subslice) (underline : s.Subslice)
  /--
  A fenced code block. `openFence`/`closeFence?` are the fences. The closing fence is
  optional because an unterminated fenced code block spans the rest of the input. The content
  `lines` exclude up to `info.openIndent` columns of indentation.
  -/
  | fencedCode (info : FenceInfo s) (openFence : s.Subslice) (closeFence? : Option s.Subslice)
    (lines : Array (VerbatimLine s))
  /--
  An indented code block: a sequence of lines that are indented four or more columns. The verbatim
  lines exclude the four column indentation.
  -/
  | indentedCode (lines : Array (VerbatimLine s))
  /-- An HTML block (CommonMark §4.6), which has at least one line. -/
  | html (lines : Array (VerbatimLine s))
  /--
  A blockquote container. `markers` contains every `>` marker, in source order, and
  `children` contains the contained blocks.
  -/
  | blockquote (markers : Array s.Subslice) (children : Array (Block.Raw s))
  /--
  A list container. All `items` are `listItem` blocks. `tight` reflects CommonMark's tight/loose
  distinction (§5.3): a tight list has no blank lines between its items or between blocks within an
  item.
  -/
  | list (kind : ListKind) (tight : Bool) (items : Array (Block.Raw s))
  /--
  A list item. `marker` is the bullet or ordered marker, and `children` are the blocks that
  the item contains.
  -/
  | listItem (marker : s.Subslice) (children : Array (Block.Raw s))
  /--
  A link reference definition: `[label]: destination "title"` (the title is optional).
  -/
  | linkRefDef (m : RefDef s)
  /--
  A thematic break (`***`, `---`, or `___`, optionally with interior spaces or tabs). `line` is the
  entire source line that produced the break.
  -/
  | thematicBreak (line : s.Subslice)
deriving Inhabited

namespace ListKind

/--
Whether two list kinds belong to the same list (that is, they have matching marker styles).

The starting number of an ordered list is irrelevant: `1.` and `5.` are the same list kind. Bullets
must use the exact same character, and ordered lists must use the same delimiter.
-/
public def sameKind : ListKind → ListKind → Bool
  | .bullet a, .bullet b => a == b
  | .ordered _ d1, .ordered _ d2 => d1 == d2
  | _, _ => false

end ListKind

/--
The surface form of a reference-style link or image.
-/
public inductive ReferenceLinkForm (s : String.Slice) where
  /--
  Full form `[text][label]`: the second brackets contain an explicit label, distinct from the link's
  text. `openBracket`/`closeBracket` are the second bracket pair.
  -/
  | full (openBracket : s.Subslice) (closeBracket : s.Subslice)
  /--
  Collapsed form `[text][]`. The second brackets are empty, and the link's text serves as the label.
  `openBracket`/`closeBracket` are the empty second bracket pair.
  -/
  | collapsed (openBracket : s.Subslice) (closeBracket : s.Subslice)
  /--
  Shortcut form `[label]`. There are no second brackets and the link's text serves as the label.
  -/
  | shortcut
deriving Inhabited

/-- The destination of a link or image. -/
public inductive LinkTarget (s : String.Slice) where
  /-- An inline target `(url)` or `(url "title")`. -/
  | inline (openParen : s.Subslice) (destination : LinkDestination s) (closeParen : s.Subslice)
    (title? : Option (LinkTitle s) := none)
  /--
  A reference target: `definition` is the link reference definition that the label resolved to, and
  `label` is the label's text: the interior of the second bracket pair in full form, and the link's
  text in collapsed and shortcut form. A reference whose label doesn't match any definition is
  plain text, brackets included, so every reference link has a definition.
  -/
  | reference (definition : RefDef s) (label : Lines s) (form : ReferenceLinkForm s)
deriving Inhabited

/--
The content of inline code (CommonMark §6.1), between its backtick strings. The lines are verbatim
source, and `text` is the string that the inline code denotes.
-/
public structure InlineCodeContent (s : String.Slice) where
  /-- The source lines. -/
  lines : Lines s
deriving Inhabited

/--
The string that inline code denotes (CommonMark §6.1): its lines joined by spaces, with one space
removed from each end when the result begins and ends with a space and is not all spaces.
-/
public def InlineCodeContent.text {s : String.Slice} (content : InlineCodeContent s) : String :=
  let joined := content.lines.text " "
  let sl := joined.toSlice
  if sl.startsWith ' ' && sl.endsWith ' ' && !sl.all (· == ' ') then
    (sl.drop 1 |>.dropEnd 1).toString
  else
    joined

/-- A parsed inline element of the source string `s`. -/
public inductive Inline (s : String.Slice) where
  /-- Plain text. -/
  | text (range : s.Subslice)
  /-- Inline code (CommonMark §6.1). -/
  | code (openTicks : s.Subslice) (content : InlineCodeContent s) (closeTicks : s.Subslice)
  /-- Italic emphasis. -/
  | italic (openDelim : s.Subslice) (content : Array (Inline s)) (closeDelim : s.Subslice)
  /-- Bold/strong emphasis. -/
  | bold (openDelim : s.Subslice) (content : Array (Inline s)) (closeDelim : s.Subslice)
  /-- Inline or reference link. The text is recursively parsed. -/
  | link (openBracket : s.Subslice) (text : Array (Inline s)) (closeBracket : s.Subslice)
    (target : LinkTarget s)
  /--
  An image. The alt content is recursively parsed as inline content (CommonMark §6.4); HTML
  rendering should flatten it to plain text for the `alt` attribute.
  -/
  | image (bang : s.Subslice) (openBracket : s.Subslice) (alt : Array (Inline s))
    (closeBracket : s.Subslice) (target : LinkTarget s)
  /--
  A hard line break (CommonMark §6.7). `marker` is the backslash or the two or more trailing spaces
  that make the line ending a hard break, and `newline` is the line ending.
  -/
  | hardBreak (marker : s.Subslice) (newline : s.Subslice)
  /--
  An autolink: `<https://...>` or `<scheme:...>` for URI form, or `<user@domain>` for email form
  (CommonMark §6.5). The URL between the angle brackets is verbatim: no backslash-escape, entity, or
  other markdown processing applies inside. `isEmail` distinguishes the email form, whose href gets
  a `mailto:` prefix when rendered to HTML.
  -/
  | autolink (openAngle : s.Subslice) (url : s.Subslice) (closeAngle : s.Subslice) (isEmail : Bool)
  /--
  Raw HTML (CommonMark §6.6): an open or closing tag, a comment, a processing instruction, a
  declaration, or a `CDATA` section. The HTML is stored verbatim.
  -/
  | html (lines : Lines s)
  /--
  A soft line break (CommonMark §6.8): the line ending between two lines of a paragraph.
  -/
  | softBreak (range : s.Subslice)
  /--
  A backslash escape `\X` of an ASCII punctuation character (CommonMark §2.4). `backslash` is the
  `\` and `char` is `X`, which is the text the escape denotes.
  -/
  | escape (backslash : s.Subslice) (char : s.Subslice)
  /--
  A character reference such as `&amp;`, `&#35;`, or `&#x1F600;` (CommonMark §2.5). The subslice
  extends from `&` through `;`. `value` is the text that the entity denotes.
  -/
  | entity (range : s.Subslice) (value : String)
deriving Inhabited

/--
A block of the source string `s`, with its inline content parsed.
-/
public inductive Block (s : String.Slice) where
  | paragraph (content : Array (Inline s))
  | atxHeading (level : Nat) (hashes : s.Subslice) (content : Array (Inline s))
    (closeHashes? : Option s.Subslice)
  | setextHeading (level : Nat) (content : Array (Inline s)) (underline : s.Subslice)
  | fencedCode (info : FenceInfo s) (openFence : s.Subslice) (closeFence? : Option s.Subslice)
    (lines : Array (VerbatimLine s))
  | indentedCode (lines : Array (VerbatimLine s))
  | html (lines : Array (VerbatimLine s))
  | blockquote (markers : Array s.Subslice) (children : Array (Block s))
  | list (kind : ListKind) (tight : Bool) (items : Array (Block s))
  | listItem (marker : s.Subslice) (children : Array (Block s))
  | linkRefDef (m : RefDef s)
  | thematicBreak (line : s.Subslice)
deriving Inhabited

attribute [inherit_doc Block.Raw.paragraph] Block.paragraph
attribute [inherit_doc Block.Raw.atxHeading] Block.atxHeading
attribute [inherit_doc Block.Raw.setextHeading] Block.setextHeading
attribute [inherit_doc Block.Raw.fencedCode] Block.fencedCode
attribute [inherit_doc Block.Raw.indentedCode] Block.indentedCode
attribute [inherit_doc Block.Raw.html] Block.html
attribute [inherit_doc Block.Raw.blockquote] Block.blockquote
attribute [inherit_doc Block.Raw.list] Block.list
attribute [inherit_doc Block.Raw.listItem] Block.listItem
attribute [inherit_doc Block.Raw.linkRefDef] Block.linkRefDef
attribute [inherit_doc Block.Raw.thematicBreak] Block.thematicBreak

variable {s : String.Slice}

/-- The subslice from `a` to `b`, or the empty subslice at `a` if `b` is before `a`. -/
public def subsliceClamped (a b : s.Pos) : s.Subslice :=
  if h : a ≤ b then s.subslice a b h else s.subslice a a (String.Slice.Pos.le_refl a)

/--
Parses a line ending at `p` in `input`: `\r\n`, `\r`, or `\n` (CommonMark §2.1). Returns the
position after the ending.
-/
public def parseLineEnding? (input : s.Subslice) (p : s.Pos) : Option s.Pos :=
  if h : p < input.endExclusive then
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let q := p.next h'
    match p.get h' with
    | '\n' => some q
    | '\r' =>
      if h2 : q < input.endExclusive then
        let h2' := String.Slice.Pos.ne_endPos_of_lt h2
        some (if q.get h2' == '\n' then q.next h2' else q)
      else some q
    | _ => none
  else none

/-- `text` without the trailing characters that satisfy `p`. -/
public def trimTrailing (text : s.Subslice) (p : Char → Bool) : s.Subslice := Id.run do
  let mut stop := text.endExclusive
  while text.startInclusive < stop do
    match stop.prev? with
    | some q =>
      if text.startInclusive ≤ q && Option.any p q.get? then stop := q else break
    | none => break
  return subsliceClamped text.startInclusive stop

/-- The subslice from the start of `first` to the end of `last`. -/
def span (first last : s.Subslice) : s.Subslice :=
  subsliceClamped first.startInclusive last.endExclusive

/-- The subslice from the start of the first line to the end of the last. -/
public def Lines.extent (lines : Lines s) : s.Subslice :=
  span lines.first lines.last

/-- The whole destination, including its angle brackets if it has them. -/
public def LinkDestination.extent (d : LinkDestination s) : s.Subslice :=
  match d.angles? with
  | some (o, c) => span o c
  | none => d.url

/-- The position just past the closing delimiter of a link target, if it has one. -/
public def LinkTarget.stop? : LinkTarget s → Option s.Pos
  | .inline _ _ closeParen _ => some closeParen.endExclusive
  | .reference _ _ (.full _ closeBracket) => some closeBracket.endExclusive
  | .reference _ _ (.collapsed _ closeBracket) => some closeBracket.endExclusive
  | .reference _ _ .shortcut => none

/--
The destination of the link or image: the inline target's, or that of the definition that the
reference resolved to.
-/
public def LinkTarget.destination : LinkTarget s → LinkDestination s
  | .inline _ destination _ _ => destination
  | .reference definition _ _ => definition.destination

/--
The title of the link or image, if it has one: the inline target's, or that of the definition that
the reference resolved to.
-/
public def LinkTarget.title? : LinkTarget s → Option (LinkTitle s)
  | .inline _ _ _ title? => title?
  | .reference definition _ _ => definition.title?

/-- The whole inline element, from its first to its last character. -/
public def Inline.extent : Inline s → s.Subslice
  | .text range => range
  | .code openTicks _ closeTicks => span openTicks closeTicks
  | .italic openDelim _ closeDelim => span openDelim closeDelim
  | .bold openDelim _ closeDelim => span openDelim closeDelim
  | .link openBracket _ closeBracket target =>
    subsliceClamped openBracket.startInclusive (target.stop?.getD closeBracket.endExclusive)
  | .image bang _ _ closeBracket target =>
    subsliceClamped bang.startInclusive (target.stop?.getD closeBracket.endExclusive)
  | .hardBreak marker newline => span marker newline
  | .autolink openAngle _ closeAngle _ => span openAngle closeAngle
  | .html lines => lines.extent
  | .softBreak range => range
  | .escape backslash char => span backslash char
  | .entity range _ => range

/-- The subslice from the start of the first element to the end of the last, if there are any. -/
public def Inline.extentOf? (inlines : Array (Inline s)) : Option s.Subslice := do
  let first ← inlines[0]?
  let last ← inlines.back?
  return span first.extent last.extent

/--
The plain text of inline content, as for an image's `alt` attribute: markup is dropped; text,
escapes, and entities contribute the text they denote; inline code contributes its content; line
breaks contribute a newline; autolinks contribute their URL; and raw HTML contributes nothing.
-/
public partial def Inline.plainText (inlines : Array (Inline s)) : String :=
  inlines.foldl (init := "") fun acc i => acc ++ go i
where
  go : Inline s → String
    | .text r => r.copy
    | .code _ content _ => content.text
    | .italic _ cs _ | .bold _ cs _ | .link _ cs _ _ | .image _ _ cs _ _ => plainText cs
    | .hardBreak .. | .softBreak _ => "\n"
    | .autolink _ url _ _ => url.copy
    | .html _ => ""
    | .escape _ char => char.copy
    | .entity _ value => value

/--
The subslice from the start of the first subslice in `rs` to the end of the last one, or `none` if
`rs` is empty.
-/
def span? (rs : Array s.Subslice) : Option s.Subslice := do
  let first ← rs[0]?
  let last ← rs.back?
  return span first last

/--
The subslice from the start of the first line to the end of the last line, or `none` if there are no
lines.
-/
def VerbatimLine.span? (lines : Array (VerbatimLine s)) : Option s.Subslice := do
  let first ← lines[0]?
  let last ← lines.back?
  return span first.source last.source

/--
The whole block, from its first delimiter to the end of its last line.
-/
public partial def Block.extent? : Block s → Option s.Subslice
  | .paragraph content => Inline.extentOf? content
  | .atxHeading _ hashes content closeHashes? =>
    let stop :=
      closeHashes?.map (·.endExclusive) <|> (Inline.extentOf? content).map (·.endExclusive)
    some (subsliceClamped hashes.startInclusive (stop.getD hashes.endExclusive))
  | .setextHeading _ content underline =>
    let start := (Inline.extentOf? content).map (·.startInclusive) |>.getD underline.startInclusive
    some (subsliceClamped start underline.endExclusive)
  | .fencedCode _ openFence closeFence? lines =>
    let stop := closeFence?.map (·.endExclusive) <|> lines.back?.map (·.source.endExclusive)
    some (subsliceClamped openFence.startInclusive (stop.getD openFence.endExclusive))
  | .indentedCode lines | .html lines => VerbatimLine.span? lines
  | .blockquote markers children => do
    let first ← markers[0]?
    let last ← markers.back?
    let stop := match span? (children.filterMap Block.extent?) with
      | some r => max last.endExclusive r.endExclusive
      | none => last.endExclusive
    return subsliceClamped first.startInclusive stop
  | .list _ _ items => span? (items.filterMap Block.extent?)
  | .listItem marker children =>
    let stop :=
      (span? (children.filterMap Block.extent?)).map (·.endExclusive) |>.getD marker.endExclusive
    some (subsliceClamped marker.startInclusive stop)
  | .linkRefDef m =>
    let stop := match m.title? with
      | some t => t.closer.endExclusive
      | none => m.destination.extent.endExclusive
    some (subsliceClamped m.openBracket.startInclusive stop)
  | .thematicBreak line => some line

/--
A normalized link label.

According to the CommonMark spec §4.7, link labels are normalized as follows:
* They are case-folded (though this implementation does not implement full Unicode case folding)
* Internal whitespace is collapsed to a single space
* Leading and trailing whitespace are removed

The constructor is private. Build values via `normalizeLabel`.
-/
public structure LinkLabel where
  private mk ::
  /--
  The label's text after normalization: case folded, with internal whitespace collapsed to single
  spaces and leading and trailing whitespace removed.
  -/
  name : String
deriving BEq, Hashable, Repr

/--
Normalizes a CommonMark link label (§6.3). `lines` are the label's source lines, and each boundary
between two lines counts as whitespace. Then:
 * Each character is case folded with `caseFold`, which covers ASCII, Latin-1, and Greek.
 * Internal sequences of whitespace become single spaces.
 * Leading and trailing whitespace is removed.
-/
public def normalizeLabel (lines : Lines s) : LinkLabel := Id.run do
  let mut out := ""
  let mut sawWs := false  -- whether we've seen whitespace since the last non-ws
  let mut sawNonWs := false  -- whether we've emitted any non-ws char yet
  for line in lines.toArray do
    for c in line.toSlice do
      -- CommonMark §6.3 normalizes "spaces, tabs, and line endings", which are exactly the
      -- characters of `Char.isWhitespace`. Unicode whitespace is not used in this part of
      -- the spec.
      if c.isWhitespace then
        sawWs := true
      else
        if sawNonWs && sawWs then out := out.push ' '
        out := pushCaseFolded out c
        sawWs := false
        sawNonWs := true
    sawWs := true
  return ⟨out⟩

/--
A document's link reference definitions by normalized label. During inline parsing, these are used
to recognize valid references.
-/
public abbrev RefTable (s : String.Slice) := Std.HashMap LinkLabel (RefDef s)
