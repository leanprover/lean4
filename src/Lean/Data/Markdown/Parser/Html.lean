/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
public import Init.Control.Option
public import Init.Control.State
import Init.Data.String.Iterate
public import Lean.Data.Markdown.InlineCursor

namespace Lean.Markdown


/-!
# Raw HTML

The tag grammar of CommonMark §6.6, which is shared by raw inline HTML and the start condition of
complete-tag HTML blocks, and the kinds of HTML block of CommonMark §4.6 with their end conditions.
-/

variable {s : String.Slice}

/-!
## Tags
-/

/-- Whether `c` may continue an HTML tag name: an ASCII letter, digit, or hyphen. -/
public def isTagNameChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- Whether `c` may begin an attribute name: an ASCII letter, `_`, or `:`. -/
def isAttributeNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':'

/-- Whether `c` may continue an attribute name: an ASCII letter, digit, `_`, `.`, `:`, or `-`. -/
def isAttributeNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'

/-- Whether `c` may be part of an unquoted attribute value. -/
def isUnquotedValueChar (c : Char) : Bool :=
  !(c.isWhitespace || c == '"' || c == '\'' || c == '=' || c == '<' || c == '>' || c == '`')

/--
Advances past spaces, tabs, and up to one line ending: the whitespace that CommonMark permits
inside an HTML tag (§6.6).
-/
def skipTagWhitespace (cur : InlineCursor s) : InlineCursor s := Id.run do
  let mut cur := cur
  let mut sawLineEnding := false
  repeat
    match cur.front? with
    | some ' ' | some '\t' => cur := cur.drop1
    | _ =>
      let some (_, afterEnding) := cur.parseLineEnding? | break
      if sawLineEnding then break
      sawLineEnding := true
      cur := afterEnding
  return cur

/-- If `cur` begins with the characters `pat`, advances past them. -/
def startsWithChars (cur : InlineCursor s) (pat : List Char) : Option (InlineCursor s) :=
  pat.foldlM (init := cur) fun cur c => if cur.front? == some c then some cur.drop1 else none

/-- Advances past the first occurrence of `pat`, or fails when there is none. -/
def advancePast (cur : InlineCursor s) (pat : List Char) : Option (InlineCursor s) := Id.run do
  let mut cur := cur
  while !cur.isEmpty do
    if let some after := startsWithChars cur pat then return some after
    cur := cur.drop1
  return none

/-- The closing delimiter of a comment, a processing instruction, a CDATA section, or a declaration. -/
public inductive HtmlCloser where
  /-- `-->` -/
  | comment
  /-- `?>` -/
  | processingInstruction
  /-- `]]>` -/
  | cdata
  /-- `>` -/
  | declaration

/-- The characters of the closer. -/
def HtmlCloser.chars : HtmlCloser → List Char
  | .comment => ['-', '-', '>']
  | .processingInstruction => ['?', '>']
  | .cdata => [']', ']', '>']
  | .declaration => ['>']

/--
For each closer, the start of the first search for it that reached the end of the input without
finding it. A search that starts at or after that position fails without reading the input.
-/
public structure HtmlScanMemo (s : String.Slice) where
  /-- The start of the first failed search for `-->`. -/
  comment? : Option s.Pos := none
  /-- The start of the first failed search for `?>`. -/
  processingInstruction? : Option s.Pos := none
  /-- The start of the first failed search for `]]>`. -/
  cdata? : Option s.Pos := none
  /-- The start of the first failed search for `>`. -/
  declaration? : Option s.Pos := none

/-- The start of the first failed search for `closer`, if there has been one. -/
def HtmlScanMemo.failedFrom? (memo : HtmlScanMemo s) : HtmlCloser → Option s.Pos
  | .comment => memo.comment?
  | .processingInstruction => memo.processingInstruction?
  | .cdata => memo.cdata?
  | .declaration => memo.declaration?

/-- Records that the search for `closer` that started at `start` failed. -/
def HtmlScanMemo.recordFailure (memo : HtmlScanMemo s) (closer : HtmlCloser) (start : s.Pos) :
    HtmlScanMemo s :=
  match closer with
  | .comment => { memo with comment? := some start }
  | .processingInstruction => { memo with processingInstruction? := some start }
  | .cdata => { memo with cdata? := some start }
  | .declaration => { memo with declaration? := some start }

/-- The monad for parsing raw HTML whose closers are searched for: failure, over an `HtmlScanMemo`. -/
public abbrev HtmlM (s : String.Slice) := OptionT (StateM (HtmlScanMemo s))

/-- The value of `x?`, or failure when it is `none`. -/
@[inline] public def HtmlM.ofOption (x? : Option α) : HtmlM s α := OptionT.mk (pure x?)

/--
Advances past the first occurrence of `closer`, or fails when there is none. A failed search is
recorded so that later searches for the same closer from the same position or beyond fail without
reading the input.
-/
def advancePastCloser (cur : InlineCursor s) (closer : HtmlCloser) : HtmlM s (InlineCursor s) := do
  if Option.any (· ≤ cur.startPos) ((← get).failedFrom? closer) then failure
  let some after := advancePast cur closer.chars
    | modify (·.recordFailure closer cur.startPos); failure
  return after

/-- Parses an attribute value at `cur`: unquoted, single-quoted, or double-quoted. -/
def parseAttributeValue? (cur : InlineCursor s) : Option (InlineCursor s) :=
  match cur.front? with
  | some '"' => advancePast cur.drop1 ['"']
  | some '\'' => advancePast cur.drop1 ['\'']
  | some c => if isUnquotedValueChar c then some (cur.skipWhile isUnquotedValueChar) else none
  | none => none

/--
Parses an HTML open tag after its `<` at `cur`, which must point at an ASCII letter: the tag name,
attributes, optional whitespace, an optional `/`, and `>`. Each attribute is preceded by whitespace.
Returns the cursor after the `>`.
-/
public def parseOpenTag? (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := cur.drop1.skipWhile isTagNameChar
  repeat
    let afterWs := skipTagWhitespace cur
    if afterWs.startPos != cur.startPos && Option.any isAttributeNameStart afterWs.front? then
      let afterName := afterWs.drop1.skipWhile isAttributeNameChar
      let beforeEq := skipTagWhitespace afterName
      if beforeEq.front? == some '=' then
        cur ← parseAttributeValue? (skipTagWhitespace beforeEq.drop1)
      else
        cur := afterName
    else
      let afterSlash := if afterWs.front? == some '/' then afterWs.drop1 else afterWs
      guard <| afterSlash.front? == some '>'
      return afterSlash.drop1
  none

/--
Parses an HTML closing tag after its `</` at `cur`: the tag name, optional whitespace, and `>`.
Returns the cursor after the `>`.
-/
public def parseClosingTag? (cur : InlineCursor s) : Option (InlineCursor s) := do
  guard <| Option.any Char.isAlpha cur.front?
  let afterName := skipTagWhitespace (cur.drop1.skipWhile isTagNameChar)
  guard <| afterName.front? == some '>'
  return afterName.drop1

/-- Parses a processing instruction after its `<?` at `cur`, through the first `?>`. -/
public def parseProcessingInstruction? (cur : InlineCursor s) : HtmlM s (InlineCursor s) :=
  advancePastCloser cur .processingInstruction

/-- Parses a comment, a CDATA section, or a declaration after its `<!` at `cur`. -/
public def parseMarkupDeclaration? (cur : InlineCursor s) : HtmlM s (InlineCursor s) := do
  if let some afterDashes := startsWithChars cur ['-', '-'] then
    -- `<!-->` and `<!--->` are complete comments; any other comment runs to the first `-->`.
    if afterDashes.front? == some '>' then return afterDashes.drop1
    if let some afterArrow := startsWithChars afterDashes ['-', '>'] then return afterArrow
    advancePastCloser afterDashes .comment
  else if let some afterCdata := startsWithChars cur ['[', 'C', 'D', 'A', 'T', 'A', '['] then
    advancePastCloser afterCdata .cdata
  else
    guard <| Option.any Char.isAlpha cur.front?
    advancePastCloser cur.drop1 .declaration

/-!
## HTML Blocks (CommonMark §4.6)
-/

/--
Parses `needle` at `p` in `input`, returning the position after it. With `ignoreCase`, ASCII letters
of the text match `needle`'s letters in either case, so `needle` should be lowercase.
-/
def matchAscii? (input : s.Subslice) (p : s.Pos) (needle : String) (ignoreCase := false) :
    Option s.Pos := Id.run do
  let mut p := p
  for c in needle.toSlice do
    if h : p < input.endExclusive then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      let d := p.get h'
      if (if ignoreCase then d.toLower else d) != c then return none
      p := p.next h'
    else
      return none
  return some p

/--
Whether `text` begins with `needle`. With `ignoreCase`, ASCII letters of the text match `needle`'s
letters in either case, so `needle` should be lowercase.
-/
public def startsWithAscii (text : s.Subslice) (needle : String) (ignoreCase := false) : Bool :=
  (matchAscii? text text.startInclusive needle ignoreCase).isSome

/--
Whether `text` is `needle`. With `ignoreCase`, ASCII letters of the text match `needle`'s letters in
either case, so `needle` should be lowercase.
-/
def equalsAscii (text : s.Subslice) (needle : String) (ignoreCase := false) : Bool :=
  matchAscii? text text.startInclusive needle ignoreCase == some text.endExclusive

/--
Whether `text` contains `needle`. With `ignoreCase`, ASCII letters of the text match `needle`'s
letters in either case, so `needle` should be lowercase.
-/
def containsAscii (text : s.Subslice) (needle : String) (ignoreCase := false) : Bool := Id.run do
  let mut p := text.startInclusive
  while h : p < text.endExclusive do
    if (matchAscii? text p needle ignoreCase).isSome then return true
    p := p.next (String.Slice.Pos.ne_endPos_of_lt h)
  return false

/--
Whether the tag name `name` is, case-insensitively, one of the raw text elements `pre`, `script`,
`style`, and `textarea`, whose HTML blocks end at an end tag.
-/
public def isRawTextTagName (name : s.Subslice) : Bool :=
  ["pre", "script", "style", "textarea"].any (equalsAscii name · (ignoreCase := true))

/--
The block-level HTML elements whose tags start an HTML block that ends before a blank line
(CommonMark §4.6, start condition 6).
-/
def blockTagNames : List String :=
  ["address", "article", "aside", "base", "basefont", "blockquote", "body", "caption", "center",
   "col", "colgroup", "dd", "details", "dialog", "dir", "div", "dl", "dt", "fieldset", "figcaption",
   "figure", "footer", "form", "frame", "frameset", "h1", "h2", "h3", "h4", "h5", "h6", "head",
   "header", "hr", "html", "iframe", "legend", "li", "link", "main", "menu", "menuitem", "nav",
   "noframes", "ol", "optgroup", "option", "p", "param", "search", "section", "summary", "table",
   "tbody", "td", "tfoot", "th", "thead", "title", "tr", "track", "ul"]

/-- Whether the tag name `name` is, case-insensitively, one of the `blockTagNames`. -/
public def isBlockTagName (name : s.Subslice) : Bool :=
  blockTagNames.any (equalsAscii name · (ignoreCase := true))

/--
Parses a complete HTML open or closing tag after its `<` at `cur`, followed by nothing but spaces
and tabs, which is the start condition of a complete-tag HTML block (CommonMark §4.6, start
condition 7). Returns the cursor at the end of the input.
-/
public def parseCompleteTagLine? (cur : InlineCursor s) : Option (InlineCursor s) := do
  let afterTag ←
    if cur.front? == some '/' then
      parseClosingTag? cur.drop1
    else
      guard <| Option.any Char.isAlpha cur.front?
      parseOpenTag? cur
  let atEnd := afterTag.skipWhile fun c => c == ' ' || c == '\t'
  guard atEnd.isEmpty
  return atEnd

/--
The kind of an HTML block (CommonMark §4.6). The kind is determined by the start condition that the
block's first line meets and selects the block's end condition.
-/
public inductive HtmlBlockKind where
  /--
  A `pre`, `script`, `style`, or `textarea` element. The block ends at a line that contains an end
  tag of any of these elements.
  -/
  | rawText
  /-- A comment. The block ends at a line that contains `-->`. -/
  | comment
  /-- A processing instruction. The block ends at a line that contains `?>`. -/
  | processingInstruction
  /-- A declaration. The block ends at a line that contains `>`. -/
  | declaration
  /-- A CDATA section. The block ends at a line that contains `]]>`. -/
  | cdata
  /-- An open or closing tag of a block-level element. The block ends before a blank line. -/
  | blockTag
  /-- A complete open or closing tag alone on its line. The block ends before a blank line. -/
  | completeTag
deriving Repr, BEq, Inhabited

namespace HtmlBlockKind

/--
Whether a block of this kind ends before a blank line, instead of at a line that contains an end
marker.
-/
public def endsAtBlankLine : HtmlBlockKind → Bool
  | .blockTag | .completeTag => true
  | _ => false

/-- Whether the first line of a block of this kind may interrupt a paragraph. -/
public def interruptsParagraph : HtmlBlockKind → Bool
  | .completeTag => false
  | _ => true

/--
Whether `line` contains the end marker of a block of this kind, which makes the line the block's
last. Kinds that end before a blank line don't have an end marker.
-/
public def endConditionMet (kind : HtmlBlockKind) (line : s.Subslice) : Bool :=
  match kind with
  | .rawText =>
    ["</pre>", "</script>", "</style>", "</textarea>"].any fun endTag =>
      containsAscii line endTag (ignoreCase := true)
  | .comment => containsAscii line "-->"
  | .processingInstruction => containsAscii line "?>"
  | .declaration => containsAscii line ">"
  | .cdata => containsAscii line "]]>"
  | .blockTag | .completeTag => false

end HtmlBlockKind
