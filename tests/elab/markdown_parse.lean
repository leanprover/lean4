import Lean.Data.Markdown

/-!
Unit tests for the Markdown parse tree: character references, backslash escapes, soft breaks,
heading levels, text decoding, and the source ranges of inline and block constructs.
-/

open Lean Markdown

def slice (src : String) (r : Syntax.Range) : String :=
  String.Pos.Raw.extract src r.start r.stop

/-- Shows each inline's constructor together with its source text or decoded value. -/
partial def showInline (src : String) : Inline → String
  | .text r => s!"text⟪{slice src r}⟫"
  | .code _ c _ => s!"code⟪{slice src c}⟫"
  | .italic _ cs _ => s!"italic[{showInlines src cs}]"
  | .bold _ cs _ => s!"bold[{showInlines src cs}]"
  | .link _ cs _ _ => s!"link[{showInlines src cs}]"
  | .image _ _ cs _ _ => s!"image[{showInlines src cs}]"
  | .hardBreak _ => "hardBreak"
  | .autolink _ u _ _ => s!"autolink⟪{slice src u}⟫"
  | .softBreak _ => "softBreak"
  | .escape _ c => s!"escape⟪{slice src c}⟫"
  | .entity _ v => s!"entity⟪{v}⟫"
where
  showInlines (src : String) (cs : Array Inline) : String :=
    " ".intercalate (cs.toList.map (showInline src))

def parse (src : String) : Array (Block (Array Inline)) :=
  parseDocument src 0 src.rawEndPos

/-- The inlines of the first paragraph of `src`. -/
def firstParagraph (src : String) : Array Inline :=
  (parse src).findSome? (fun | .paragraph lines => lines[0]? | _ => none) |>.getD #[]

def showParagraph (src : String) : String :=
  showInline.showInlines src (firstParagraph src)

/-! ## Escapes, character references, and soft breaks -/

/-- info: "text⟪a ⟫ escape⟪*⟫ text⟪ b ⟫ entity⟪&⟫ text⟪ c ⟫ entity⟪#⟫ text⟪ ⟫ entity⟪A⟫" -/
#guard_msgs in #eval showParagraph "a \\* b &amp; c &#35; &#x41;"

/-- info: "text⟪&bogus; &#; &#x; &amp ⟫ entity⟪�⟫ text⟪ ⟫ entity⟪�⟫" -/
#guard_msgs in #eval showParagraph "&bogus; &#; &#x; &amp &#0; &#xD800;"

/-- info: "text⟪a⟫ softBreak text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\nb"

/-- info: "text⟪a⟫ hardBreak text⟪b⟫" -/
#guard_msgs in #eval showParagraph "a\\\nb"

/-- info: "text⟪\\a ⟫ escape⟪\\⟫ text⟪ ⟫ escape⟪&⟫ text⟪amp;⟫" -/
#guard_msgs in #eval showParagraph "\\a \\\\ \\&amp;"

/-- info: "code⟪&amp; \\*⟫ text⟪ ⟫ autolink⟪https://x.y/?a&amp;b⟫" -/
#guard_msgs in #eval showParagraph "`&amp; \\*` <https://x.y/?a&amp;b>"

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

/-! ## Source ranges -/

def inlineRanges (src : String) : List String :=
  (firstParagraph src).toList.map fun i => slice src i.range

/-- info: ["[x](/u)", " ", "![a][r]", " ", "<ab:c>", " ", "`c`", " ", "**b**", " ", "[r]", " ", "\\*", " ", "&lt;"] -/
#guard_msgs in #eval inlineRanges "[x](/u) ![a][r] <ab:c> `c` **b** [r] \\* &lt;\n\n[r]: /u"

def blockRanges (src : String) : List String :=
  (parse src).toList.filterMap fun b => (b.range? Inline.rangeOf?).map (slice src)

/-- info: ["> # h\n> para", "- a\n  b\n- c", "[r]: /u \"t\"", "```lean\ncode\n```", "***", "    code"] -/
#guard_msgs in #eval blockRanges "> # h\n> para\n\n- a\n  b\n- c\n\n[r]: /u \"t\"\n\n```lean\ncode\n```\n\n***\n\n    code\n"
