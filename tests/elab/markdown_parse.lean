import Lean.Data.Markdown

/-!
Unit tests for the Markdown parse tree: character references, backslash escapes, soft breaks,
heading levels, text decoding, and the extent of inline and block constructs.
-/

open Lean Markdown

/-- Shows each inline's constructor together with its source text or decoded value. -/
partial def showInline {s : String.Slice} : Inline s → String
  | .text r => s!"text⟪{r.copy}⟫"
  | .code _ lines _ => s!"code⟪{"\n".intercalate (lines.toList.map (·.copy))}⟫"
  | .italic _ cs _ => s!"italic[{showInlines cs}]"
  | .bold _ cs _ => s!"bold[{showInlines cs}]"
  | .link _ cs _ _ => s!"link[{showInlines cs}]"
  | .image _ _ cs _ _ => s!"image[{showInlines cs}]"
  | .hardBreak m _ => s!"hardBreak⟪{m.copy}⟫"
  | .autolink _ u _ _ => s!"autolink⟪{u.copy}⟫"
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

/-- info: "text⟪a⟫ softBreak text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\nb"

/-- info: "text⟪a⟫ hardBreak⟪\\⟫ text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\\\nb"

/-- info: "text⟪a⟫ hardBreak⟪  ⟫ text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a  \nb"

/-- info: "text⟪\\a ⟫ escape⟪\\⟫ text⟪ ⟫ escape⟪&⟫ text⟪amp;⟫" -/
#guard_msgs in #eval showParagraph "\\a \\\\ \\&amp;"

/-- info: "code⟪&amp; \\*⟫ text⟪ ⟫ autolink⟪https://x.y/?a&amp;b⟫" -/
#guard_msgs in #eval showParagraph "`&amp; \\*` <https://x.y/?a&amp;b>"

/-!
## Emphasis with leftover delimiters

An opener left over after part of its sequence matched a closer keeps the sequence's original length
due to rule 9 of CommonMark §6.2.
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
## Emphasis next to Unicode punctuation and whitespace

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

/-- info: "italic[text⟪α⟫] text⟪β⟫" -/
#guard_msgs in #eval showParagraph "*α*β"

/-- info: [false, true] -/
#guard_msgs in #eval [hasEmphasis "*\u00A0a\u00A0*", hasEmphasis "*a*"]

/-! ## Text decoding -/

/-- info: "a*b&#&amp;&bogus;\\q" -/
#guard_msgs in #eval decodeText "a\\*b&amp;&#35;\\&amp;&bogus;\\q"

/-- info: [some "&", none, some "A", some "�", some "�", none, none, none, none, none] -/
#guard_msgs in #eval [characterReference? "amp", characterReference? "Amp", characterReference? "#x41",
  characterReference? "#x110000", characterReference? "#xD800", characterReference? "#12345678",
  characterReference? "#00000065", characterReference? "#x0000041", characterReference? "#",
  characterReference? ""]

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
    [t.opener.copy, "\n".intercalate (t.content.toList.map (·.copy)), t.closer.copy]
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
    | .link _ _ _ (.reference d _ _) =>
      some (d.destination.url.copy, d.title?.map fun t => "\n".intercalate (t.content.toList.map (·.copy)))
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
## Content that continues onto the next line

The content of a code span, a link title, or a reference label that continues onto the next line of
a container has one subslice per line, without the container's prefix.
-/

/-- The lines of every code span in the paragraphs of `src`, descending into blockquotes. -/
partial def codeLines (src : String) : List (List String) :=
  go (parse src).toList
where
  go {s : String.Slice} (blocks : List (Block s)) : List (List String) :=
    blocks.flatMap fun
      | .paragraph content => content.toList.filterMap fun
        | .code _ lines _ => some (lines.toList.map (·.copy))
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
          some (label.toList.map (·.copy))
        | _ => none
      | .linkRefDef m => [m.label.toList.map (·.copy)]
      | .blockquote _ children => go children.toList
      | _ => []

/-- info: [["foo", "bar"], ["x", "y"], ["z"], ["foo", "bar"], ["x y"], ["z"]] -/
#guard_msgs in #eval labelLines "> [a][foo\n> bar] [x\n> y] [z]\n>\n> [foo\n> bar]: /u\n> [x y]: /v\n> [z]: /w"

def blockRanges (src : String) : List String :=
  (parse src).toList.filterMap fun b => b.extent?.map (·.copy)

/-- info: ["> # h\n> para", "- a\n  b\n- c", "[r]: /u \"t\"", "```lean\ncode\n```", "***", "code"] -/
#guard_msgs in #eval blockRanges "> # h\n> para\n\n- a\n  b\n- c\n\n[r]: /u \"t\"\n\n```lean\ncode\n```\n\n***\n\n    code\n"

/-!
## Indented documents

Up to `indent` leading spaces of each line are indentation of the document as a whole, as in an
indented docstring, and are skipped before the line is parsed.
-/

/-- Shows the block structure of a document, with paragraph text and code block lines. -/
partial def showBlock {s : String.Slice} : Block s → String
  | .paragraph content => s!"paragraph⟪{showInline.showInlines content}⟫"
  | .indentedCode lines => s!"indentedCode{repr (lines.map (·.2))}"
  | .fencedCode _ _ _ lines => s!"fencedCode{repr (lines.map (·.copy))}"
  | .list _ _ items => s!"list[{", ".intercalate (items.toList.map showBlock)}]"
  | .listItem _ children => s!"item[{", ".intercalate (children.toList.map showBlock)}]"
  | .atxHeading _ _ content _ => s!"heading⟪{showInline.showInlines content}⟫"
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

-- An indented document with a continuation line indented less than four more columns, an indented
-- code block, and a list item whose continuation and second paragraph are indented to its content.
/--
info: ["paragraph⟪text⟪Intro⟫ softBreak text⟪continued⟫⟫", "indentedCode#[\"code line\", \"  more code\"]",
 "list[item[paragraph⟪text⟪item⟫ softBreak text⟪item continued⟫⟫, paragraph⟪text⟪item paragraph⟫⟫]]"]
-/
#guard_msgs in #eval showDocument
  "    Intro\n      continued\n\n        code line\n          more code\n\n    - item\n      item continued\n\n      item paragraph\n" 4

-- Indentation is counted in spaces; a line indented less than `indent` loses only its own spaces.
/-- info: ["heading⟪text⟪h⟫⟫", "paragraph⟪text⟪p⟫⟫"] -/
#guard_msgs in #eval showDocument "  # h\n\n    p" 4

/-!
## Code fences

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
