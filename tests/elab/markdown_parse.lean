import Lean.Data.Markdown

/-!
Unit tests for the Markdown parse tree: character references, backslash escapes, soft breaks,
heading levels, text decoding, and the source ranges of inline and block constructs.
-/

open Lean Markdown

/-- Shows each inline's constructor together with its source text or decoded value. -/
partial def showInline {s : String.Slice} : Inline s → String
  | .text r => s!"text⟪{r.copy}⟫"
  | .code _ c _ => s!"code⟪{c.copy}⟫"
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
  (firstParagraph src).toList.map fun i => i.range.copy

/-- info: ["[x](/u)", " ", "![a][r]", " ", "<ab:c>", " ", "`c`", " ", "**b**", " ", "[r]", " ", "\\*", " ", "&lt;"] -/
#guard_msgs in #eval inlineRanges "[x](/u) ![a][r] <ab:c> `c` **b** [r] \\* &lt;\n\n[r]: /u"

/-- The opener, text, and closer of every link title in `src`, including those of reference definitions. -/
def titleParts (src : String) : List (List String) :=
  (parse src).toList.flatMap fun
    | .paragraph content => content.toList.filterMap fun
      | .link _ _ _ (.inline _ _ _ (some t)) | .image _ _ _ _ (.inline _ _ _ (some t)) =>
        some [t.opener.copy, t.content.copy, t.closer.copy]
      | _ => none
    | .linkRefDef m => (m.title?.map fun t => [t.opener.copy, t.content.copy, t.closer.copy]).toList
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
    | .link _ _ _ (.reference d _) => some (d.destination.url.copy, d.title?.map (·.content.copy))
    | _ => none

/-- info: [("/u", none), ("v", some "t")] -/
#guard_msgs in #eval referenceTargets "[a][r] [b]\n\n[r]: /u\n[b]: <v> 't'"

def blockRanges (src : String) : List String :=
  (parse src).toList.filterMap fun b => b.range?.map (·.copy)

/-- info: ["> # h\n> para", "- a\n  b\n- c", "[r]: /u \"t\"", "```lean\ncode\n```", "***", "code"] -/
#guard_msgs in #eval blockRanges "> # h\n> para\n\n- a\n  b\n- c\n\n[r]: /u \"t\"\n\n```lean\ncode\n```\n\n***\n\n    code\n"
