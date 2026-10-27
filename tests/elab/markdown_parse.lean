import Lean.Data.Markdown

/-!
Unit tests for the Markdown parse tree: character references, backslash escapes, soft breaks,
heading levels, text decoding, and the extent of inline and block constructs.
-/

open Lean Markdown

/-- Shows each inline's constructor together with its source text or decoded value. -/
partial def showInline {s : String.Slice} : Inline s → String
  | .text r => s!"text⟪{r.copy}⟫"
  | .code _ content _ => s!"code⟪{content.lines.text}⟫"
  | .italic _ cs _ => s!"italic[{showInlines cs}]"
  | .bold _ cs _ => s!"bold[{showInlines cs}]"
  | .link _ cs _ _ => s!"link[{showInlines cs}]"
  | .image _ _ cs _ _ => s!"image[{showInlines cs}]"
  | .hardBreak m _ => s!"hardBreak⟪{m.copy}⟫"
  | .autolink _ u _ _ => s!"autolink⟪{u.copy}⟫"
  | .math _ content _ display => s!"{if display then "displayMath" else "math"}⟪{content.text}⟫"
  | .html lines => s!"html⟪{lines.text}⟫"
  | .softBreak _ => "softBreak"
  | .escape _ c => s!"escape⟪{c.copy}⟫"
  | .entity _ v => s!"entity⟪{v}⟫"
where
  showInlines {s : String.Slice} (cs : Array (Inline s)) : String :=
    " ".intercalate (cs.toList.map showInline)

def parse (src : String) : Array (Block src.toSlice) :=
  parseDocument src.toSlice

/-- The inlines of the first paragraph of `src`. -/
def firstParagraph (src : String) : Array (Inline src.toSlice) :=
  (parse src).findSome? (fun | .paragraph content => some content | _ => none) |>.getD #[]

def showParagraph (src : String) : String :=
  showInline.showInlines (firstParagraph src)

/-! ## Escapes, character references, and soft breaks -/

/-- info: "text⟪a ⟫ escape⟪*⟫ text⟪ b ⟫ entity⟪&⟫ text⟪ c ⟫ entity⟪#⟫ text⟪ ⟫ entity⟪A⟫" -/
#guard_msgs in #eval showParagraph "a \\* b &amp; c &#35; &#x41;"

/-- info: "text⟪&bogus; &#; &#x; &amp ⟫ entity⟪�⟫ text⟪ ⟫ entity⟪�⟫" -/
#guard_msgs in #eval showParagraph "&bogus; &#; &#x; &amp &#0; &#xD800;"

-- A numeric reference has at most 7 decimal or 6 hexadecimal digits (CommonMark §2.5). Within that
-- limit, a value above U+10FFFF is U+FFFD; beyond it, the reference is text.
/-- info: "entity⟪�⟫ text⟪ &#99999999; ⟫ entity⟪�⟫ text⟪ &#x1100000;⟫" -/
#guard_msgs in #eval showParagraph "&#9999999; &#99999999; &#x110000; &#x1100000;"

/-- info: "text⟪a⟫ softBreak text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\nb"

/-- info: "text⟪a⟫ hardBreak⟪\\⟫ text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\\\nb"

/-- info: "text⟪a⟫ hardBreak⟪  ⟫ text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a  \nb"

-- Spaces before a soft break are removed (CommonMark §6.8); a tab is text.
/-- info: "text⟪z\t⟫ softBreak text⟪b⟫" -/
#guard_msgs in #eval showParagraph "z\t\nb"

/-- info: "text⟪\\a ⟫ escape⟪\\⟫ text⟪ ⟫ escape⟪&⟫ text⟪amp;⟫" -/
#guard_msgs in #eval showParagraph "\\a \\\\ \\&amp;"

/-- info: "code⟪&amp; \\*⟫ text⟪ ⟫ autolink⟪https://x.y/?a&amp;b⟫" -/
#guard_msgs in #eval showParagraph "`&amp; \\*` <https://x.y/?a&amp;b>"

-- Backtick sequences without a closing sequence of the same length are text (CommonMark §6.1),
-- also after a sequence that was closed.
/-- info: ["text⟪`a ``b ```c⟫", "code⟪a` ⟫ text⟪b``⟫"] -/
#guard_msgs in #eval [showParagraph "`a ``b ```c", showParagraph "``a` ``b``"]

-- A second code span after an unclosed longer sequence is still a code span.
/-- info: "text⟪x ``a⟫ code⟪b⟫ text⟪ ⟫ code⟪c⟫" -/
#guard_msgs in #eval showParagraph "x ``a`b` `c`"

/-!
## Emphasis with Leftover Delimiters

An opener that is left over after part of its sequence matched a closer keeps the sequence's
original length due to rule 9 of CommonMark §6.2.
-/

/-- info: "italic[text⟪a⟫] text⟪*⟫ italic[text⟪b⟫]" -/
#guard_msgs in #eval showParagraph "*a***b*"

/-!
## Brackets

Links and images follow the bracket-stack procedure of the CommonMark appendix: a link may not
contain another link, an image may contain links, emphasis does not cross a link boundary, and
unmatched brackets are text. The nesting depth of brackets does not affect parsing time.
-/

/-- info: "text⟪[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]⟫" -/
#guard_msgs in #eval showParagraph ("".pushn '[' 30 ++ "".pushn ']' 30)

/-- info: "text⟪[foo ⟫ link[text⟪bar⟫] text⟪](/v)⟫" -/
#guard_msgs in #eval showParagraph "[foo [bar](/u)](/v)"

/-- info: "image[text⟪a ⟫ link[text⟪b⟫]]" -/
#guard_msgs in #eval showParagraph "![a [b](/u)](/v)"

/-- info: "text⟪[a ⟫ italic[link[text⟪b⟫]] text⟪](/v)⟫" -/
#guard_msgs in #eval showParagraph "[a *[b](/u)*](/v)"

/-- info: "text⟪*⟫ link[text⟪a*⟫]" -/
#guard_msgs in #eval showParagraph "*[a*](/u)"

-- `[bar` is not a link label, so `[foo]` is a shortcut reference.
/-- info: "link[text⟪foo⟫] text⟪[bar⟫" -/
#guard_msgs in #eval showParagraph "[foo][bar\n\n[foo]: /u"

-- `[bar]` is a link label, so `[foo]` is not a shortcut reference, and `[bar]` is not defined.
/-- info: "text⟪[foo][bar]⟫" -/
#guard_msgs in #eval showParagraph "[foo][bar]\n\n[foo]: /u"

/-!
## Raw HTML

Tags, comments, processing instructions, declarations, and CDATA sections are raw HTML (CommonMark
§6.6), kept verbatim with one subslice per line. Text that merely contains `<` is not.
-/

/-- info: "html⟪<b class=\"x\">⟫ text⟪a⟫ html⟪</b>⟫" -/
#guard_msgs in #eval showParagraph "<b class=\"x\">a</b>"

-- At the start of a line, the comment would begin an HTML block instead.
/-- info: "text⟪x ⟫ html⟪<!-- c -->⟫ text⟪ ⟫ html⟪<?php x ?>⟫ text⟪ ⟫ html⟪<!DOCTYPE html>⟫ text⟪ ⟫ html⟪<![CDATA[ x ]]>⟫" -/
#guard_msgs in #eval showParagraph "x <!-- c --> <?php x ?> <!DOCTYPE html> <![CDATA[ x ]]>"

/-- info: "text⟪a < b, <|> and <$> and <33> and <a / >⟫" -/
#guard_msgs in #eval showParagraph "a < b, <|> and <$> and <33> and <a / >"

-- An attribute value may be unquoted, and a tag may be self-closing.
/-- info: "html⟪<a href=u>⟫ html⟪<br/>⟫" -/
#guard_msgs in #eval showParagraph "<a href=u><br/>"

-- A tag that continues onto the next line has one subslice per source line.
/-- info: "html⟪<a\nhref=\"u\">⟫" -/
#guard_msgs in #eval showParagraph "<a\nhref=\"u\">"

-- An autolink is preferred over a tag.
/-- info: "autolink⟪https://e.com⟫" -/
#guard_msgs in #eval showParagraph "<https://e.com>"

-- A search for a closer that reaches the end of the input is remembered, so a later opener of the
-- same kind is text without another search, while openers of other kinds still find their closers.
/-- info: "text⟪x <!-- a <!-- b ⟫ html⟪<?c?>⟫ text⟪ <!-- d ⟫ html⟪<![CDATA[e]]>⟫ text⟪ <!f <!g⟫" -/
#guard_msgs in #eval showParagraph "x <!-- a <!-- b <?c?> <!-- d <![CDATA[e]]> <!f <!g"

/-!
## Emphasis Next to Unicode Punctuation and Whitespace

The flanking rules classify characters by Unicode category for Latin-1, Greek, and the symbol
blocks, so `_` emphasis opens after and closes before a mathematical symbol, a `*` after a currency
sign cannot close, and a no-break space is whitespace.
-/

/-- Whether the first paragraph of `src` contains emphasis. -/
def hasEmphasis (src : String) : Bool :=
  (firstParagraph src).any fun | .italic .. | .bold .. => true | _ => false

/-- info: "text⟪→⟫ italic[text⟪x⟫] text⟪→⟫" -/
#guard_msgs in #eval showParagraph "→_x_→"

/-- info: "text⟪*£*bravo⟫" -/
#guard_msgs in #eval showParagraph "*£*bravo"

-- A currency sign outside the Basic Multilingual Plane is punctuation too.
/-- info: "text⟪*𞋿*a⟫" -/
#guard_msgs in #eval showParagraph "*𞋿*a"

/-- info: "italic[text⟪α⟫] text⟪β⟫" -/
#guard_msgs in #eval showParagraph "*α*β"

/-- info: [false, true] -/
#guard_msgs in #eval [hasEmphasis "*\u00A0a\u00A0*", hasEmphasis "*a*"]

/-! ## Text decoding -/

/-- info: "a*b&#&amp;&bogus;\\q" -/
#guard_msgs in #eval decodeText "a\\*b&amp;&#35;\\&amp;&bogus;\\q"

/-- The decoding of the character reference `&body;`. -/
def charRef? (body : String) : Option String :=
  characterReference? body.toSlice.toSubslice

/-- info: [some "&", none, some "A", some "�", some "�", none, none, none, none, none] -/
#guard_msgs in #eval [charRef? "amp", charRef? "Amp", charRef? "#x41", charRef? "#x110000",
  charRef? "#xD800", charRef? "#12345678", charRef? "#00000065", charRef? "#x0000041", charRef? "#",
  charRef? ""]

/-! ## Heading levels -/

def headingLevels (src : String) : List Nat :=
  (parse src).toList.filterMap fun
    | .atxHeading level .. => some level
    | .setextHeading level .. => some level
    | _ => none

/-- info: [1, 3, 1, 2] -/
#guard_msgs in #eval headingLevels "# a\n\n### b\n\nc\n===\n\nd\n---"

/-! ## Extents -/

def inlineRanges (src : String) : List String :=
  (firstParagraph src).toList.map fun i => i.extent.copy

/-- info: ["[x](/u)", " ", "![a][r]", " ", "<ab:c>", " ", "`c`", " ", "**b**", " ", "[r]", " ", "\\*", " ", "&lt;"] -/
#guard_msgs in #eval inlineRanges "[x](/u) ![a][r] <ab:c> `c` **b** [r] \\* &lt;\n\n[r]: /u"

/--
The opener, text, and closer of every link title in `src`, including those of reference definitions,
descending into blockquotes. The text's lines are joined with newlines.
-/
partial def titleParts (src : String) : List (List String) :=
  go (parse src).toList
where
  parts {s : String.Slice} (t : LinkTitle s) : List String :=
    [t.opener.copy, t.content.text, t.closer.copy]
  go {s : String.Slice} (blocks : List (Block s)) : List (List String) :=
    blocks.flatMap fun
      | .paragraph content => content.toList.filterMap fun
        | .link _ _ _ (.inline _ _ _ (some t)) | .image _ _ _ _ (.inline _ _ _ (some t)) =>
          some (parts t)
        | _ => none
      | .linkRefDef m => (m.title?.map parts).toList
      | .blockquote _ children => go children.toList
      | _ => []

/-- info: [["\"", "a b", "\""], ["'", "c", "'"], ["(", "d", ")"], ["(", "e\nf", ")"]] -/
#guard_msgs in #eval titleParts "[x](/u \"a b\") ![y](/v 'c')\n\n[r]: /w (d)\n\n[q]: /z\n  (e\nf)"

/-- The angle brackets, if any, and the URL of every destination in `src`. -/
def destinationParts (src : String) : List (List String) :=
  let parts (d : LinkDestination src.toSlice) : List String :=
    if let some (o, c) := d.angles? then [o.copy, d.url.copy, c.copy] else [d.url.copy]
  (parse src).toList.flatMap fun
    | .paragraph content => content.toList.filterMap fun
      | .link _ _ _ (.inline _ d _ _) | .image _ _ _ _ (.inline _ d _ _) => some (parts d)
      | _ => none
    | .linkRefDef m => [parts m.destination]
    | _ => []

/-- info: [["<", "u v", ">"], ["w"], ["<", "x", ">"], ["y"], ["<", "", ">"]] -/
#guard_msgs in #eval destinationParts "[a](<u v>) ![b](w)\n\n[r]: <x>\n\n[q]: y\n\n[e]: <>"

/-- The URL and title of the definition that each reference link in the first paragraph resolved to. -/
def referenceTargets (src : String) : List (String × Option String) :=
  (firstParagraph src).toList.filterMap fun
    | .link _ _ _ (.reference (.inDocument d) _ _) =>
      some (d.destination.url.copy, d.title?.map (·.content.text))
    | _ => none

/-- info: [("/u", none), ("v", some "t")] -/
#guard_msgs in #eval referenceTargets "[a][r] [b]\n\n[r]: /u\n[b]: <v> 't'"

-- Labels are case folded for Latin-1 and Greek letters, including `ß` to `ss`, final sigma to sigma,
-- and the micro sign to `μ`.
/-- info: [("/1", none), ("/2", none), ("/3", none), ("/4", none), ("/5", none)] -/
#guard_msgs in #eval referenceTargets
  "[É][] [Straße] [ΑΓΩ] [ς] [µ]\n\n[é]: /1\n[STRASSE]: /2\n[αγω]: /3\n[Σ]: /4\n[Μ]: /5"

-- Letters outside the covered blocks are compared as written.
/-- info: [] -/
#guard_msgs in #eval referenceTargets "[Я]\n\n[я]: /u"

/-!
## Content That Continues onto the Next Line

The content of inline code, a link title, or a reference label that continues onto the next line of
a container has one subslice per line, without the container's prefix.
-/

/-- The lines of all inline code in the paragraphs of `src`, descending into blockquotes. -/
partial def codeLines (src : String) : List (List String) :=
  go (parse src).toList
where
  go {s : String.Slice} (blocks : List (Block s)) : List (List String) :=
    blocks.flatMap fun
      | .paragraph content => content.toList.filterMap fun
        | .code _ content _ => some content.lines.copy.toList
        | _ => none
      | .blockquote _ children => go children.toList
      | _ => []

/-- info: [["a", "b"], ["c", ""]] -/
#guard_msgs in #eval codeLines "> `a\n> b` `c\n> `"

/-- info: [["\"", "t\nu", "\""], ["(", "d\ne", ")"]] -/
#guard_msgs in #eval titleParts "> [x](/u \"t\n> u\")\n>\n> [r]: /v\n> (d\n> e)"

/--
The label lines of every reference link and reference definition in `src`, in source order, descending
into blockquotes.
-/
partial def labelLines (src : String) : List (List String) :=
  go (parse src).toList
where
  go {s : String.Slice} (blocks : List (Block s)) : List (List String) :=
    blocks.flatMap fun
      | .paragraph content => content.toList.filterMap fun
        | .link _ _ _ (.reference _ label _) | .image _ _ _ _ (.reference _ label _) =>
          some label.copy.toList
        | _ => none
      | .linkRefDef m => [m.label.copy.toList]
      | .blockquote _ children => go children.toList
      | _ => []

/-- info: [["foo", "bar"], ["x", "y"], ["z"], ["foo", "bar"], ["x y"], ["z"]] -/
#guard_msgs in #eval labelLines "> [a][foo\n> bar] [x\n> y] [z]\n>\n> [foo\n> bar]: /u\n> [x y]: /v\n> [z]: /w"

def blockRanges (src : String) : List String :=
  (parse src).toList.filterMap fun b => b.extent?.map (·.copy)

/-- info: ["> # h\n> para", "- a\n  b\n- c", "[r]: /u \"t\"", "```lean\ncode\n```", "***", "code"] -/
#guard_msgs in #eval blockRanges "> # h\n> para\n\n- a\n  b\n- c\n\n[r]: /u \"t\"\n\n```lean\ncode\n```\n\n***\n\n    code\n"

/-!
## Indented Documents

Up to `indent` leading spaces of each line are indentation of the document as a whole, as in an
indented docstring, and are skipped before the line is parsed.
-/

/-- Shows the block structure of a document, with paragraph text and code block lines. -/
partial def showBlock {s : String.Slice} : Block s → String
  | .paragraph content => s!"paragraph⟪{showInline.showInlines content}⟫"
  | .indentedCode lines => s!"indentedCode{repr (lines.map (·.text))}"
  | .fencedCode _ _ _ lines => s!"fencedCode{repr (lines.map (·.text))}"
  | .list _ tight items =>
    s!"{if tight then "list" else "looseList"}[{", ".intercalate (items.toList.map showBlock)}]"
  | .setextHeading _ content _ => s!"setext⟪{showInline.showInlines content}⟫"
  | .linkRefDef _ => "refDef"
  | .listItem _ children => s!"item[{", ".intercalate (children.toList.map showBlock)}]"
  | .atxHeading _ _ content _ => s!"heading⟪{showInline.showInlines content}⟫"
  | .blockquote _ children => s!"blockquote[{", ".intercalate (children.toList.map showBlock)}]"
  | .html lines => s!"html{repr (lines.map (·.text))}"
  | _ => "other"

def showDocument (src : String) (indent : Nat) : List String :=
  (parseDocument src.toSlice indent).toList.map showBlock

/-- info: ["paragraph⟪text⟪x⟫⟫", "paragraph⟪text⟪y⟫⟫"] -/
#guard_msgs in #eval showDocument "x\n\n    y" 4

/-- info: ["paragraph⟪text⟪x⟫⟫", "indentedCode#[\"y\"]"] -/
#guard_msgs in #eval showDocument "x\n\n    y" 0

-- An unindented first line, as when the content starts on the line of the opening delimiter.
/-- info: ["heading⟪text⟪h⟫⟫", "heading⟪text⟪h2⟫⟫"] -/
#guard_msgs in #eval showDocument "# h\n    ## h2" 4

/-- info: ["heading⟪text⟪h⟫⟫", "indentedCode#[\"## h2\"]"] -/
#guard_msgs in #eval showDocument "# h\n    ## h2" 0

-- An indented document with a continuation line that is indented less than four more columns, an
-- indented code block, and a list item whose continuation and second paragraph are indented to its
-- content.
/--
info: ["paragraph⟪text⟪Intro⟫ softBreak text⟪continued⟫⟫", "indentedCode#[\"code line\", \"  more code\"]",
 "looseList[item[paragraph⟪text⟪item⟫ softBreak text⟪item continued⟫⟫, paragraph⟪text⟪item paragraph⟫⟫]]"]
-/
#guard_msgs in #eval showDocument
  "    Intro\n      continued\n\n        code line\n          more code\n\n    - item\n      item continued\n\n      item paragraph\n" 4

-- Indentation is counted in spaces; a line that is indented less than `indent` loses only its own
-- spaces.
/-- info: ["heading⟪text⟪h⟫⟫", "paragraph⟪text⟪p⟫⟫"] -/
#guard_msgs in #eval showDocument "  # h\n\n    p" 4

-- The content lines of a fenced code block exclude the opening fence's indentation, and no more.
/-- info: ["fencedCode#[\"code\", \" more\", \"x\"]"] -/
#guard_msgs in #eval showDocument "  ```\n  code\n   more\n x\n  ```\n" 0

-- In an indented document, the document's indentation is removed first and the fence's indentation
-- is relative to what remains, so each content line loses both.
/-- info: ["paragraph⟪text⟪Intro⟫⟫", "fencedCode#[\"code\", \"  indented\", \"x\"]"] -/
#guard_msgs in #eval showDocument "    Intro\n\n      ```\n      code\n        indented\n     x\n      ```\n" 4

/-!
## List Markers after Paragraph Text

A list marker on the line after a paragraph's text starts a list only if its item may interrupt a
paragraph (CommonMark §5.2): the item has content, and an ordered list starts at 1. This applies
when the paragraph is the innermost open block. When a container did not continue on the marker's
line, any marker starts a list.
-/

-- At the content column of an item whose paragraph is open, a start other than 1 or an empty item
-- is paragraph text.
/-- info: ["list[item[paragraph⟪text⟪a⟫ softBreak text⟪b⟫ softBreak text⟪5. c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "1. a\n   b\n   5. c\n" 0

/-- info: ["list[item[paragraph⟪text⟪a⟫ softBreak text⟪b⟫ softBreak text⟪*⟫⟫]]"] -/
#guard_msgs in #eval showDocument "* a\n  b\n  *\n" 0

-- A start of 1 begins a nested list.
/-- info: ["list[item[paragraph⟪text⟪a⟫ softBreak text⟪b⟫⟫, list[item[paragraph⟪text⟪c⟫⟫]]]]"] -/
#guard_msgs in #eval showDocument "1. a\n   b\n   1. c\n" 0

-- After an item that did not continue, a sibling marker with any start, or an empty marker of
-- another kind, starts a list.
/-- info: ["list[item[paragraph⟪text⟪a⟫⟫], item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "1. a\n5. b\n" 0

/-- info: ["list[item[paragraph⟪text⟪a⟫⟫]]", "list[item[]]"] -/
#guard_msgs in #eval showDocument "1. a\n-\n" 0

-- After a blockquote that did not continue, likewise.
/-- info: ["blockquote[paragraph⟪text⟪a⟫⟫]", "list[item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "> a\n5. b\n" 0

/-!
## Lazy Continuation Lines

A line that lazily continues a paragraph has its leading whitespace removed (CommonMark §4.8), also
when the paragraph so far ends with a hard break or consists of link reference definitions.
-/

/-- info: ["blockquote[paragraph⟪hardBreak⟪\\⟫ text⟪e⟫⟫]"] -/
#guard_msgs in #eval showDocument ">\\\n e\n" 0

/-- info: ["blockquote[refDef, paragraph⟪text⟪b⟫⟫]"] -/
#guard_msgs in #eval showDocument ">[r]:u\n b\n" 0

/-!
## Blank Lines after an Empty Item

An item whose marker is alone on its line ends at the next line when that line is blank, whatever
its indentation (CommonMark §5.2).
-/

/-- info: ["list[item[]]", "paragraph⟪text⟪o⟫⟫"] -/
#guard_msgs in #eval showDocument "-\n  \n  o\n" 0

/-!
## List Tightness

A list is loose when two blocks of one of its items are separated by a blank line (CommonMark
§5.3). Blank lines after the list, and blank lines inside an indented code block, are not separators.
-/

/-- info: ["list[item[paragraph⟪text⟪a⟫⟫]]", "paragraph⟪text⟪b⟫⟫"] -/
#guard_msgs in #eval showDocument "- a\n\n\nb\n" 0

/-- info: ["looseList[item[paragraph⟪text⟪a⟫⟫, paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- a\n\n\n  b\n" 0

-- The blank line after an indented code block is consumed by the block, and still separates it from
-- the paragraph that follows.
/-- info: ["looseList[item[indentedCode#[\"e\"], paragraph⟪text⟪h⟫⟫]]"] -/
#guard_msgs in #eval showDocument "1.     e\n\n   h\n" 0

/-- info: ["list[item[indentedCode#[\"e\", \"\", \"f\"]]]"] -/
#guard_msgs in #eval showDocument "1.     e\n\n       f\n" 0

-- A blank line inside a nested list separates the outer item from its sibling too, but a blank line
-- inside a blockquote belongs to the blockquote.
/-- info: ["looseList[item[paragraph⟪text⟪a⟫⟫, list[item[paragraph⟪text⟪b⟫⟫]]], item[paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- a\n  - b\n\n- c\n" 0

/-- info: ["looseList[item[blockquote[paragraph⟪text⟪a⟫⟫]], item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- > a\n\n- b\n" 0

/-- info: ["list[item[blockquote[list[item[]]]], item[paragraph⟪text⟪f⟫⟫]]"] -/
#guard_msgs in #eval showDocument "-\n  >-\n  >\n- f\n" 0

/-- info: ["list[item[paragraph⟪text⟪a⟫⟫, blockquote[list[item[paragraph⟪text⟪b⟫⟫]]], paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- a\n  > - b\n  >\n  c\n" 0

-- A blank line before a new item of the nested list makes only the nested list loose; before a new
-- block of the outer item, the outer list.
/-- info: ["list[item[paragraph⟪text⟪a⟫⟫, looseList[item[paragraph⟪text⟪c⟫⟫], item[]]]]"] -/
#guard_msgs in #eval showDocument "- a\n  - c\n\n  -\n" 0

/-- info: ["looseList[item[paragraph⟪text⟪a⟫⟫, list[item[paragraph⟪text⟪b⟫⟫]], list[item[paragraph⟪text⟪c⟫⟫]]]]"] -/
#guard_msgs in #eval showDocument "- a\n  - b\n\n  1. c\n" 0

/-- info: ["looseList[item[paragraph⟪text⟪a⟫⟫, blockquote[paragraph⟪text⟪b⟫⟫]]]"] -/
#guard_msgs in #eval showDocument "- a\n\n  > b\n" 0

-- A thematic break is a block of the item, so a blank line after it separates it from the
-- paragraph that follows.
/-- info: ["looseList[item[other, paragraph⟪text⟪o⟫⟫]]"] -/
#guard_msgs in #eval showDocument "-\n  ---\n\n  o\n" 0

-- A blank line that an indented code block or an HTML block consumes still separates list items,
-- unless the block continues after it, as in cmark. A blank line inside fenced code is content.
/-- info: ["looseList[item[indentedCode#[\"code\"]], item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "-     code\n\n- b\n" 0

/-- info: ["list[item[indentedCode#[\"a\", \"\", \"b\"], paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "-     a\n\n      b\n  c\n" 0

/-- info: ["looseList[item[html#[\"<!--\", \"\"]], item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- <!--\n\n- b\n" 0

/-- info: ["list[item[html#[\"<!--\", \"\", \"-->\"], paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- <!--\n\n  -->\n  c\n" 0

/-- info: ["list[item[fencedCode#[\"\"]], item[paragraph⟪text⟪b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- ```\n\n  ```\n- b\n" 0

-- A blank line between an empty item and the next item separates them, so the list is loose
-- (CommonMark §5.3), as cmark and commonmark.js also read it.
/-- info: ["looseList[item[], item[paragraph⟪text⟪bar⟫⟫]]"] -/
#guard_msgs in #eval showDocument "-\n\n- bar\n" 0

/-- info: ["looseList[item[paragraph⟪text⟪a⟫⟫], item[], item[paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "* a\n*\n\n* c\n" 0

-- Without the blank line, the list is tight.
/-- info: ["list[item[paragraph⟪text⟪a⟫⟫], item[], item[paragraph⟪text⟪c⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- a\n-\n- c\n" 0

/-!
## Parentheses in Link Destinations

CommonMark §6.3 allows implementations to limit the nesting of parentheses in an unbracketed
destination, as long as at least three levels work. This implementation limits nesting to 32.
-/

/-- The paragraph `[a](` followed by `depth` nested parentheses around `u`, then `)`. -/
def nestedDestination (depth : Nat) : String :=
  "[a](" ++ "".pushn '(' depth ++ "u" ++ "".pushn ')' depth ++ ")"

/-- info: true -/
#guard_msgs in #eval (showParagraph (nestedDestination 32)).startsWith "link["

/-- info: false -/
#guard_msgs in #eval (showParagraph (nestedDestination 33)).startsWith "link["

/-!
## Link Titles

A parenthesized title may contain `(` and `)` only backslash-escaped, and a title must be separated
from the destination by whitespace (CommonMark §6.3).
-/

/-- info: "text⟪[a](/u (x(y))⟫" -/
#guard_msgs in #eval showParagraph "[a](/u (x(y))"

/-- info: [["\"", "t", "\""]] -/
#guard_msgs in #eval titleParts "[a](<b> \"t\")"

/-- info: "text⟪[a](⟫ html⟪<b>⟫ text⟪\"title\")⟫" -/
#guard_msgs in #eval showParagraph "[a](<b>\"title\")"

/-- info: [["(", "x\\(y", ")"]] -/
#guard_msgs in #eval titleParts "[a](/u (x\\(y))"

/-!
## Backslashes in Labels, Destinations, and Titles

A backslash escapes the ASCII punctuation character after it (CommonMark §2.4). Before any other
character it is an ordinary character, so it neither hides a space or line ending nor spans one.
-/

/-- info: "text⟪[a](/u\\ v)⟫" -/
#guard_msgs in #eval showParagraph "[a](/u\\ v)"

/-- info: ["refDef", "paragraph⟪text⟪`⟫⟫"] -/
#guard_msgs in #eval showDocument "[r]:\n\\\n`\n" 0

/-- info: ["list[item[paragraph⟪text⟪[r]:⟫ softBreak text⟪\\ b⟫⟫]]"] -/
#guard_msgs in #eval showDocument "1. [r]:\n\\ b\n" 0

/-- info: ["paragraph⟪text⟪[a\\⟫⟫", "paragraph⟪text⟪b]: /u⟫⟫"] -/
#guard_msgs in #eval showDocument "[a\\\n\nb]: /u\n" 0

/-!
## Canceled Setext Headings

A setext heading whose text is nothing but link reference definitions is not a heading. Its
underline is paragraph text, which the following paragraph or setext heading continues.
-/

/-- info: ["refDef", "setext⟪text⟪===⟫ softBreak text⟪bar⟫⟫"] -/
#guard_msgs in #eval showDocument "[foo]: /url\n===\nbar\n---\n" 0

/-- info: ["refDef", "paragraph⟪text⟪===⟫ softBreak link[text⟪foo⟫]⟫"] -/
#guard_msgs in #eval showDocument "[foo]: /url\n===\n[foo]\n" 0

/-- info: ["refDef", "paragraph⟪text⟪===⟫⟫"] -/
#guard_msgs in #eval showDocument "[foo]: /url\n===\n" 0

-- The paragraph that the underline starts is still open, so the next line may continue it lazily,
-- and a blank line ends it.
/-- info: ["blockquote[refDef, paragraph⟪text⟪-⟫ softBreak text⟪h⟫⟫]"] -/
#guard_msgs in #eval showDocument ">[r]:\n]\n>-\nh\n" 0

/-- info: ["refDef", "paragraph⟪text⟪=⟫⟫", "paragraph⟪text⟪]⟫⟫"] -/
#guard_msgs in #eval showDocument "[o]:l\n=\n\n]\n" 0

-- A backslash is a non-whitespace character of a label, whatever it escapes.
/-- info: ["refDef", "paragraph⟪link[text⟪\\ ⟫]⟫"] -/
#guard_msgs in #eval showDocument "[\\ ]: /url\n\n[\\ ]\n" 0

/-!
## Tabs in Verbatim Blocks

A tab ends inside a container prefix or a block's indentation when the columns it spans straddle
that boundary (CommonMark §2.2). The remaining columns of the tab are leading spaces of the line in
code blocks and HTML blocks, on blank lines too, as in cmark.
-/

-- After `1.`, the content column is 3, so a tab leaves one column; after `*`, two.
/-- info: ["list[item[html#[\" <v>\"]]]"] -/
#guard_msgs in #eval showDocument "1.\n\t<v>\n" 0

/-- info: ["list[item[html#[\"  <e>\"]]]"] -/
#guard_msgs in #eval showDocument "*\n\t<e>\n" 0

/-- info: ["list[item[indentedCode#[\"  foo\"]]]"] -/
#guard_msgs in #eval showDocument "-\t\tfoo\n" 0

-- A fence that is indented one column takes one column of a tab on each content line.
/-- info: ["fencedCode#[\"   \"]"] -/
#guard_msgs in #eval showDocument " ```\n\t\n```\n" 0

-- A blank line in a list item keeps the remaining column of its tab.
/-- info: ["list[item[fencedCode#[\" \"]]]"] -/
#guard_msgs in #eval showDocument "1) ~~~\n\t\n   ~~~\n" 0

-- A tab that begins after the indentation is content, even at a column that is no tab stop.
/-- info: ["looseList[item[paragraph⟪text⟪x⟫⟫, indentedCode#[\"\\tfoo\"]]]"] -/
#guard_msgs in #eval showDocument "1. x\n\n       \tfoo\n" 0

-- Indentation that continues past a partly consumed tab uses up the tab's remaining columns.
/-- info: ["list[item[indentedCode#[\".\"]]]"] -/
#guard_msgs in #eval showDocument "+\n\t  .\n" 0

-- The remaining column of a tab is indentation of a closing fence.
/-- info: ["list[item[fencedCode#[]]]"] -/
#guard_msgs in #eval showDocument "2) ```\n\t```\n" 0

/-!
## HTML Blocks

An HTML block (CommonMark §4.6) starts with a line that meets one of seven start conditions, after up
to three spaces of indentation, and ends with the line that meets the matching end condition. For raw
text elements, comments, processing instructions, declarations, and CDATA sections, the ending line
is part of the block. For block-level tags and complete tags, the block ends before a blank line.
The lines are verbatim.
-/

-- A raw text element ends at an end tag, which may be on the start line and need not match the
-- start tag. Blank lines are part of the block.
/-- info: ["html#[\"<pre>\", \"  x\", \"\", \"</STYLE>\"]", "paragraph⟪text⟪ok⟫⟫"] -/
#guard_msgs in #eval showDocument "<pre>\n  x\n\n</STYLE>\nok\n" 0

/-- info: ["html#[\"<script>a()</script>\"]", "paragraph⟪text⟪ok⟫⟫"] -/
#guard_msgs in #eval showDocument "<script>a()</script>\nok\n" 0

/--
info: ["html#[\"<!-- a\", \"b -->\"]", "html#[\"<?php\", \"?>\"]", "html#[\"<!DOCTYPE html>\"]",
 "html#[\"<![CDATA[\", \"x\", \"]]>\"]", "paragraph⟪text⟪ok⟫⟫"]
-/
#guard_msgs in #eval showDocument "<!-- a\nb -->\n<?php\n?>\n<!DOCTYPE html>\n<![CDATA[\nx\n]]>\nok\n" 0

-- A block-level tag interrupts a paragraph, and the block ends before a blank line.
/--
info: ["paragraph⟪text⟪para⟫⟫", "html#[\"<div>\", \"*not emphasis*\"]", "paragraph⟪italic[text⟪emphasis⟫]⟫",
 "html#[\"</div>\"]"]
-/
#guard_msgs in #eval showDocument "para\n<div>\n*not emphasis*\n\n*emphasis*\n</div>\n" 0

-- A complete tag on a line of its own starts a block, except after a paragraph line; a tag that is
-- followed by other text is inline HTML.
/--
info: ["paragraph⟪text⟪para⟫ softBreak html⟪<span>⟫⟫", "html#[\"<span class='x'>  \", \"text\"]",
 "paragraph⟪html⟪<span>⟫ text⟪ text⟫⟫"]
-/
#guard_msgs in #eval showDocument "para\n<span>\n\n<span class='x'>  \ntext\n\n<span> text\n" 0

-- Tag names are case-insensitive, and a closing or self-closing tag also starts a block.
/-- info: ["html#[\"<DIV/>\"]", "html#[\"</Table>\"]"] -/
#guard_msgs in #eval showDocument "<DIV/>\n\n</Table>\n" 0

-- A complete tag of a raw text element starts a block too, as in cmark and commonmark.js, which
-- ignore the exclusion of these elements from §4.6 start condition 7.
/-- info: ["html#[\"<pre/>\", \"foo\"]", "html#[\"</pre>\", \"bar\"]"] -/
#guard_msgs in #eval showDocument "<pre/>\nfoo\n\n</pre>\nbar\n" 0

/-- info: ["paragraph⟪text⟪< div> and <33>⟫⟫"] -/
#guard_msgs in #eval showDocument "< div> and <33>\n" 0

-- A tag name begins with an ASCII letter and may continue with digits and hyphens.
/-- info: ["paragraph⟪text⟪<===⟫ softBreak text⟪<-> <a b=>⟫⟫", "html#[\"<a->\"]"] -/
#guard_msgs in #eval showDocument "<===\n<-> <a b=>\n\n<a->\n" 0

-- Up to three spaces of indentation are allowed and kept; four make indented code.
/-- info: ["html#[\"   <div>\"]", "indentedCode#[\"<div>\"]"] -/
#guard_msgs in #eval showDocument "   <div>\n\n    <div>\n" 0

-- The block ends with its container.
/-- info: ["blockquote[html#[\"<div>\", \"a\"]]", "paragraph⟪text⟪b⟫⟫"] -/
#guard_msgs in #eval showDocument "> <div>\n> a\nb\n" 0

/-- info: ["<div>\na", "<!-- c -->"] -/
#guard_msgs in #eval blockRanges "<div>\na\n\n<!-- c -->\n"

/-!
## Code Fences

A closing fence may be followed by spaces or tabs and nothing else. The info string is trimmed of
leading and trailing spaces or tabs.
-/

/-- The info string of every fenced code block in `src`. -/
def infoStrings (src : String) : List (Option String) :=
  (parse src).toList.filterMap fun
    | .fencedCode info _ _ _ => some (info.infoString?.map (·.copy))
    | _ => none

/-- info: ["fencedCode#[\"code\"]", "paragraph⟪text⟪after⟫⟫"] -/
#guard_msgs in #eval showDocument "```\ncode\n```\t \n\nafter" 0

/-- info: ["fencedCode#[\"code\", \"``` x\", \"after\"]"] -/
#guard_msgs in #eval showDocument "```\ncode\n``` x\nafter" 0

/-- info: [some "lean", some "lean"] -/
#guard_msgs in #eval infoStrings "```\tlean\t\n```\n\n``` lean \n```"

/-!
## Line Endings

A line ending is `\r\n`, `\r`, or `\n` (CommonMark §2.1). Verbatim lines and the lines of inline
content exclude the ending, and a soft or hard break is the whole ending.
-/

/-- info: ["heading⟪text⟪head⟫⟫", "list[item[paragraph⟪text⟪item⟫⟫]]"] -/
#guard_msgs in #eval showDocument "# head\r\n\r\n- item\r\n" 0

/-- info: ["setext⟪text⟪foo⟫⟫"] -/
#guard_msgs in #eval showDocument "foo\r\n===\r\n" 0

/-- info: ["text⟪a⟫ softBreak text⟪b⟫", "text⟪a⟫ softBreak text⟪b⟫"] -/
#guard_msgs in #eval [showParagraph "a\r\nb", showParagraph "a\rb"]

/-- info: ["text⟪a⟫ hardBreak⟪\\⟫ text⟪b⟫", "text⟪a⟫ hardBreak⟪  ⟫ text⟪b⟫"] -/
#guard_msgs in #eval [showParagraph "a\\\r\nb", showParagraph "a  \r\nb"]

/-- The source text of each soft break in the first paragraph of `src`. -/
def softBreakTexts (src : String) : Array String :=
  (firstParagraph src).filterMap fun | .softBreak r => some r.copy | _ => none

/-- info: #["\x0d\n"] -/
#guard_msgs in #eval softBreakTexts "a\r\nb"

/-- info: [["a", "b"]] -/
#guard_msgs in #eval codeLines "`a\r\nb`"

/-- info: ["indentedCode#[\"x\", \"y\"]", "html#[\"<div>\", \"x\", \"</div>\"]"] -/
#guard_msgs in #eval showDocument "    x\r\n    y\r\n\r\n<div>\r\nx\r\n</div>\r\n" 0

/-- info: [["\"", "t", "\""]] -/
#guard_msgs in #eval titleParts "[r]: /u\r\n  \"t\"\r\n\r\n[r]"

/-- info: ["blockquote[paragraph⟪text⟪a⟫ softBreak text⟪b⟫⟫]"] -/
#guard_msgs in #eval showDocument "> a\r\n> b\r\n" 0

/-- info: ["looseList[item[paragraph⟪text⟪c⟫⟫, paragraph⟪text⟪d⟫⟫]]"] -/
#guard_msgs in #eval showDocument "- c\r\n\r\n  d\r\n" 0

/-!
## LaTeX Math

The `latexMath` extension recognizes `$…$` and `$$…$$` with the following rules, which are
compatible with `md4c`:

* a dollar sequence opens only at the start of a line or after whitespace or punctuation
* a dollar sequence closes only at the end of a line or before whitespace or punctuation
* potentially-closing dollar sequences match the most recent opener of the same length

Without the extension, dollar signs are ordinary text.
-/

/-- The inlines of the first paragraph of `src`, with LaTeX math enabled. -/
def showMathParagraph (src : String) : String :=
  let blocks := parseDocument src.toSlice (extensions := { latexMath := true })
  let content := blocks.findSome? (fun | .paragraph content => some content | _ => none) |>.getD #[]
  showInline.showInlines content

/-- info: "text⟪a ⟫ math⟪x_1⟫ text⟪ b ⟫ displayMath⟪y⟫ text⟪ c⟫" -/
#guard_msgs in #eval showMathParagraph "a $x_1$ b $$y$$ c"

/-- info: "text⟪a $x_1$ b⟫" -/
#guard_msgs in #eval showParagraph "a $x_1$ b"

-- The closer matches the most recent opener, and a match discards the openers before it.
/-- info: "text⟪$a ⟫ math⟪b⟫ text⟪ c⟫" -/
#guard_msgs in #eval showMathParagraph "$a $b$ c"

-- Openers and closers match only when their lengths agree, and the match discards the pending
-- opener of the other length.
/-- info: "text⟪$a ⟫ displayMath⟪b⟫ text⟪ c$⟫" -/
#guard_msgs in #eval showMathParagraph "$a $$b$$ c$"

-- A dollar sign inside a word neither opens nor closes.
/-- info: "text⟪a$b$ $c$d⟫" -/
#guard_msgs in #eval showMathParagraph "a$b$ $c$d"

-- Escaped dollar signs and dollar signs inside inline code take no part, so here the first and last
-- dollar signs match, and the escape and the code between them are content.
/-- info: "math⟪a \\$ `$b$` c⟫" -/
#guard_msgs in #eval showMathParagraph "$a \\$ `$b$` c$"

/-- info: "text⟪a ⟫ escape⟪$⟫ text⟪ ⟫ code⟪$b$⟫ text⟪ c⟫" -/
#guard_msgs in #eval showMathParagraph "a \\$ `$b$` c"

-- Markdown syntax inside a span is content, so emphasis cannot cross a span.
/-- info: "math⟪a*b⟫ text⟪ and ⟫ math⟪c*d⟫" -/
#guard_msgs in #eval showMathParagraph "$a*b$ and $c*d$"

-- Three or more dollar signs are text.
/-- info: "text⟪$$$a$$$⟫" -/
#guard_msgs in #eval showMathParagraph "$$$a$$$"

-- Multiple-line joining rules: a line's leading whitespace is dropped, and its line ending becomes
-- a space unless the previous line already ends with one.
/-- info: ["math⟪a  + b⟫", "math⟪a\t b⟫"] -/
#guard_msgs in #eval [showMathParagraph "$a  \n  +\n b$", showMathParagraph "$a\t\nb$"]

/-!
## External Reference Definitions

A caller may supply additional reference definitions that are not present in the document. The
document's definitions take precedence unless an external definition sets `overrideDocument`.
-/

/--
The destination text of each reference link in the first paragraph, and whether it is external.
-/
def externalTargets (src : String) : List (String × Bool) :=
  let externalRefs : Std.HashMap String ExternalRef :=
    ({} : Std.HashMap String ExternalRef)
      |>.insert "Knuth 1984" { destination := "references.html#knuth", title? := some "Knuth" }
      |>.insert "r" { destination := "/external" }
      |>.insert "o" { destination := "/override", overrideDocument := true }
      |>.insert " " { destination := "/blank" }
      |>.insert "Dup" { destination := "/dup-upper" }
      |>.insert "dup" { destination := "/dup-lower" }
  let blocks := parseDocument src.toSlice (externalRefs := externalRefs)
  let content := blocks.findSome? (fun | .paragraph content => some content | _ => none) |>.getD #[]
  content.toList.filterMap fun
    | .link _ _ _ target@(.reference refTarget _ _) =>
      some (target.destination, refTarget matches .external ..)
    | _ => none

/-- info: [("references.html#knuth", true), ("/document", false), ("/document", false)] -/
#guard_msgs in #eval externalTargets "[knuth 1984] [r] [x][r]\n\n[r]: /document\n"

-- External labels that normalize alike: the lexicographically least label's definition is used.
/-- info: [("/dup-upper", true), ("/dup-upper", true)] -/
#guard_msgs in #eval externalTargets "[DUP] [dup]\n"

/-- info: [("/external", true)] -/
#guard_msgs in #eval externalTargets "[r]\n"

/-- info: [("/override", true), ("/override", true)] -/
#guard_msgs in #eval externalTargets "[o] [O]\n\n[o]: /document\n"

-- A link label must contain a character that is not whitespace, so brackets around nothing or
-- around spaces are text even when an external definition is keyed by a blank label.
/-- info: [] -/
#guard_msgs in #eval externalTargets "[ ] [] [x][ ] [x][]\n"
