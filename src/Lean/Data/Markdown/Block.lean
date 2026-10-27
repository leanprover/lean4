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
public import Init.Data.String.FindPos
public import Lean.Data.Markdown.Inline
public import Lean.Data.Markdown.InlineSource

namespace Lean.Markdown

/-!
# Blocks

The blocks of a parsed Markdown document: the raw blocks that the first pass produces, and the
blocks with parsed inline content that the second pass produces.
-/

/--
A count of columns. Indentation is measured in columns (CommonMark §2.2): a space is one column,
and a tab advances to the next tab stop, which is the next multiple of four.
-/
public structure Columns where
  /-- The number of columns. -/
  count : Nat
deriving DecidableEq, Repr, Inhabited

namespace Columns

@[inline] public instance : OfNat Columns n where
  ofNat := ⟨n⟩

public instance : LE Columns where
  le a b := a.count ≤ b.count

public instance : LT Columns where
  lt a b := a.count < b.count

@[inline] public instance (a b : Columns) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.count ≤ b.count))

@[inline] public instance (a b : Columns) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.count < b.count))

@[inline] public instance : Add Columns where
  add a b := ⟨a.count + b.count⟩

@[inline] public instance : Sub Columns where
  sub a b := ⟨a.count - b.count⟩

/-- The columns after a space. -/
@[inline] public def space (c : Columns) : Columns := ⟨ c.count + 1 ⟩

/-- The width of a tab at `c`: the columns up to the next tab stop. -/
@[inline] public def tabWidth (c : Columns) : Columns := ⟨4 - c.count % 4⟩

/-- The columns after a tab: the next tab stop. -/
@[inline] public def tab (c : Columns) : Columns := c + c.tabWidth

end Columns

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
  The indentation of the opening fence's first character. The content lines exclude up to this much
  indentation.
  -/
  openIndent : Columns
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
A block of the source string `s` after the first pass, which determines the type and extent of every
block but does not parse inline content. The content of a paragraph or heading is an `InlineSource`.
-/
public inductive Block.Raw (s : String.Slice) where
  /--
  A paragraph: a sequence of consecutive non-blank lines that did not open any other leaf.
  -/
  | paragraph (content : InlineSource s)
  /--
  An ATX heading (the usual kind). `level` is the number of opening `#` characters, `hashes` is that
  opening sequence, and `closeHashes?` an optional closing sequence.
  -/
  | atxHeading (level : Nat) (hashes : s.Subslice) (content : InlineSource s)
      (closeHashes? : Option s.Subslice)
  /--
  A setext heading (CommonMark §4.3): one or more lines of paragraph text that are followed by an
  `underline` (`===` for level 1, `---` for level 2).
  -/
  | setextHeading (level : Nat) (content : InlineSource s) (underline : s.Subslice)
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
  distinction (§5.3): a tight list doesn't have blank lines between its items or between blocks
  within an item.
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
  line's content from its first marker to its last.
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
