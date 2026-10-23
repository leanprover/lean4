/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
public import Init.While
import Init.Data.String.Iterate
public import Lean.Data.Markdown.InlineSource

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

/-- Advances past the characters that satisfy `p`. -/
def skipChars (cur : InlineCursor s) (p : Char → Bool) : InlineCursor s := Id.run do
  let mut cur := cur
  while Option.any p cur.front? do
    cur := cur.drop1
  return cur

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

/-- Parses an attribute value at `cur`: unquoted, single-quoted, or double-quoted. -/
def parseAttributeValue? (cur : InlineCursor s) : Option (InlineCursor s) :=
  match cur.front? with
  | some '"' => advancePast cur.drop1 ['"']
  | some '\'' => advancePast cur.drop1 ['\'']
  | some c => if isUnquotedValueChar c then some (skipChars cur isUnquotedValueChar) else none
  | none => none

/--
Parses an HTML open tag after its `<` at `cur`, which must point at an ASCII letter: the tag name,
attributes, optional whitespace, an optional `/`, and `>`. Each attribute is preceded by whitespace.
Returns the cursor after the `>`.
-/
public def parseOpenTag? (cur : InlineCursor s) : Option (InlineCursor s) := do
  let mut cur := skipChars cur.drop1 isTagNameChar
  repeat
    let afterWs := skipTagWhitespace cur
    if afterWs.startPos != cur.startPos && Option.any isAttributeNameStart afterWs.front? then
      let afterName := skipChars afterWs.drop1 isAttributeNameChar
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
  let afterName := skipTagWhitespace (skipChars cur.drop1 isTagNameChar)
  guard <| afterName.front? == some '>'
  return afterName.drop1

/-- Parses a processing instruction after its `<?` at `cur`, through the first `?>`. -/
public def parseProcessingInstruction? (cur : InlineCursor s) : Option (InlineCursor s) :=
  advancePast cur ['?', '>']

/-- Parses a comment, a CDATA section, or a declaration after its `<!` at `cur`. -/
public def parseMarkupDeclaration? (cur : InlineCursor s) : Option (InlineCursor s) := do
  if let some afterDashes := startsWithChars cur ['-', '-'] then
    -- `<!-->` and `<!--->` are complete comments; any other comment runs to the first `-->`.
    if afterDashes.front? == some '>' then return afterDashes.drop1
    if let some afterArrow := startsWithChars afterDashes ['-', '>'] then return afterArrow
    advancePast afterDashes ['-', '-', '>']
  else if let some afterCdata := startsWithChars cur ['[', 'C', 'D', 'A', 'T', 'A', '['] then
    advancePast afterCdata [']', ']', '>']
  else
    guard <| Option.any Char.isAlpha cur.front?
    advancePast cur.drop1 ['>']

/-!
## HTML blocks (CommonMark §4.6)
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
condition 7). Open tags of the raw text elements are excluded. Returns the cursor at the end of the
input.
-/
public def parseCompleteTagLine? (cur : InlineCursor s) : Option (InlineCursor s) := do
  let afterTag ←
    if cur.front? == some '/' then
      parseClosingTag? cur.drop1
    else
      guard <| Option.any Char.isAlpha cur.front?
      let afterName := skipChars cur.drop1 isTagNameChar
      guard !(isRawTextTagName (subsliceClamped cur.startPos afterName.startPos))
      parseOpenTag? cur
  let atEnd := skipChars afterTag fun c => c == ' ' || c == '\t'
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
last. Kinds that end before a blank line have no end marker.
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
