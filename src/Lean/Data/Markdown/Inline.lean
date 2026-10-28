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
import Lean.Data.Markdown.Unicode.CaseFolding
import Lean.Data.Markdown.Text
public import Lean.Data.Markdown.Lines

namespace Lean.Markdown

/-!
# Inline Elements

The inline elements of a parsed Markdown document, the parts of a link, and the link reference
definitions and external references that reference links resolve to.
-/

/--
Non-standard extensions that can be optionally enabled.
-/
public structure Extensions where
  /--
  LaTeX math, which is `$…$` for inline math and `$$…$$` for display math.
  -/
  latexMath : Bool := false
deriving Inhabited

/--
The title of a link, image, or link reference definition, which is written `"…"`, `'…'`, or `(…)`.
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
The destination of a link, image, or link reference definition, which is a URL, optionally in angle
brackets.
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
A reference definition from outside the document that is supplied by the parser's caller. The
destination URL and title are used as-is. Backslash escapes and character references in them are
not decoded.
-/
public structure ExternalRef where
  /-- The destination URL. -/
  destination : String
  /-- The optional title. -/
  title? : Option String := none
  /--
  Whether this definition takes precedence over a link reference definition in the document that
  has the same label.
  -/
  overrideDocument : Bool := false
deriving Inhabited

/--
What a reference link may resolve to.
-/
public inductive RefTarget (s : String.Slice) where
  /-- A link reference definition in the document. -/
  | inDocument (definition : RefDef s)
  /-- A definition from outside the document. -/
  | external (ref : ExternalRef)
deriving Inhabited

/--
The destination of a reference target, with backslash escapes and character references decoded.
-/
public def RefTarget.destination {s : String.Slice} : RefTarget s → String
  | .inDocument definition => definition.destination.text
  | .external ref => ref.destination

/--
The title of a reference target, if it has one, with backslash escapes and character references
decoded.
-/
public def RefTarget.title? {s : String.Slice} : RefTarget s → Option String
  | .inDocument definition => definition.title?.map (·.text)
  | .external ref => ref.title?

/--
The surface form of a reference-style link or image.
-/
public inductive ReferenceLinkForm (s : String.Slice) where
  /--
  Full form `[text][label]`, in which the second brackets contain an explicit label, distinct from
  the link's text. `openBracket`/`closeBracket` are the second bracket pair.
  -/
  | full (openBracket : s.Subslice) (closeBracket : s.Subslice)
  /--
  Collapsed form `[text][]`. The second brackets are empty, and the link's text serves as the label.
  `openBracket`/`closeBracket` are the empty second bracket pair.
  -/
  | collapsed (openBracket : s.Subslice) (closeBracket : s.Subslice)
  /--
  Shortcut form `[label]`. There aren't any second brackets, and the link's text serves as the
  label.
  -/
  | shortcut
deriving Inhabited

/-- The destination of a link or image. -/
public inductive LinkTarget (s : String.Slice) where
  /-- An inline target `(url)` or `(url "title")`. -/
  | inline (openParen : s.Subslice) (destination : LinkDestination s) (closeParen : s.Subslice)
    (title? : Option (LinkTitle s) := none)
  /--
  A reference target, in which `refTarget` is what the label resolved to, and `label` is the
  label's text.

  The label text is the interior of the second bracket pair in full form, and the link's text in
  collapsed and shortcut form. In Markdown, seeming links to labels that don't match any definition
  in the document are not in fact links (they are just plain text), so every reference link has a
  resolved target.
  -/
  | reference (refTarget : RefTarget s) (label : Lines s) (form : ReferenceLinkForm s)
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
The content of LaTeX math between the dollar signs. The lines are verbatim source.

Use `MathContent.text` to extract the normalized single-line string representation.
-/
public structure MathContent (s : String.Slice) where
  /-- The source lines. -/
  lines : Lines s
deriving Inhabited

/--
The normalized single-line string representation of LaTeX math.

Leading spaces and tabs are removed from all lines after the first, and line endings become spaces
unless the line already ends with a space.
-/
public def MathContent.text {s : String.Slice} (content : MathContent s) : String := Id.run do
  let isBlank (c : Char) := c == ' ' || c == '\t'
  let mut out := content.lines.first.copy
  for line in content.lines.toArray[1:] do
    if !out.endsWith " " then out := out.push ' '
    out := out ++ (line.copy.dropWhile isBlank).toString
  return out

/--
The string that inline code denotes (CommonMark §6.1), which is its lines joined by spaces, with
one space removed from each end when the result begins and ends with a space and is not all spaces.
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
  An autolink, which is `<https://...>` or `<scheme:...>` for URI form, or `<user@domain>` for
  email form (CommonMark §6.5). The URL between the angle brackets is verbatim. Backslash escapes,
  character references, and other Markdown syntax are not processed inside it. `isEmail`
  distinguishes the email form, whose href gets a `mailto:` prefix when rendered to HTML.
  -/
  | autolink (openAngle : s.Subslice) (url : s.Subslice) (closeAngle : s.Subslice) (isEmail : Bool)
  /--
  LaTeX math, produced only when the `latexMath` extension is enabled.

  This extension uses `$…$` for inline math and `$$…$$` for display math, with `display` set to
  `true` for the latter.
  -/
  | math (openDollars : s.Subslice) (content : MathContent s) (closeDollars : s.Subslice)
    (display : Bool)
  /--
  Raw HTML (CommonMark §6.6), which is an open or closing tag, a comment, a processing instruction,
  a declaration, or a `CDATA` section. The HTML is stored verbatim.
  -/
  | html (lines : Lines s)
  /--
  A soft line break (CommonMark §6.8), which is the line ending between two lines of a paragraph.
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

variable {s : String.Slice}

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
The source of the destination of the link or image in the original document.

This may be that of an inline target's, or that of the reference definition that a label resolved
to.  A reference that resolved to an external definition has none.
-/
public def LinkTarget.destinationSource? : LinkTarget s → Option (LinkDestination s)
  | .inline _ destination _ _ => some destination
  | .reference (.inDocument definition) _ _ => some definition.destination
  | .reference (.external ..) _ _ => none

/--
The source of the title of the link or image, if it has one.

This may be that of an inline target, or that of the link reference definition that the reference
resolved to. References that resolve to external definitions have none.
-/
public def LinkTarget.titleSource? : LinkTarget s → Option (LinkTitle s)
  | .inline _ _ _ title? => title?
  | .reference (.inDocument definition) _ _ => definition.title?
  | .reference (.external ..) _ _ => none

/--
The destination of the link or image, with backslash escapes and character references decoded.
-/
public def LinkTarget.destination : LinkTarget s → String
  | .inline _ destination _ _ => destination.text
  | .reference refTarget _ _ => refTarget.destination

/--
The title of the link or image, if it has one, with backslash escapes and character references
decoded.
-/
public def LinkTarget.title? : LinkTarget s → Option String
  | .inline _ _ _ title? => title?.map (·.text)
  | .reference refTarget _ _ => refTarget.title?

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
  | .math openDollars _ closeDollars _ => span openDollars closeDollars
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
The plain text of inline content, as for an image's `alt` attribute:
* Markup is dropped
* Text, escapes, and entities are mapped to their plain text
* Inline code and math are mapped to their literal content
* Line breaks are mapped to newlines
* Autolinks are mapped to their URLs
* Raw HTML is deleted
-/
public partial def Inline.plainText (inlines : Array (Inline s)) : String :=
  inlines.foldl (init := "") fun acc i => acc ++ go i
where
  go : Inline s → String
    | .text r => r.copy
    | .code _ content _ => content.text
    | .math _ content _ _ => content.text
    | .italic _ cs _ | .bold _ cs _ | .link _ cs _ _ | .image _ _ cs _ _ => plainText cs
    | .hardBreak .. | .softBreak _ => "\n"
    | .autolink _ url _ _ => url.copy
    | .html _ => ""
    | .escape _ char => char.copy
    | .entity _ value => value

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
  The label's text after normalization.

  Normalization consists of case folding, collapsing internal whitespace to single spaces, and
  trimming leading and trailing whitespace.
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

/-- The normalized form of `label`, for a label that is given as a string. -/
public def LinkLabel.ofString (label : String) : LinkLabel :=
  normalizeLabel (Lines.singleton label.toSlice.toSubslice)

/--
A mapping from normalized link labels to a document's reference targets.
-/
public abbrev RefTable (s : String.Slice) := Std.HashMap LinkLabel (RefTarget s)
