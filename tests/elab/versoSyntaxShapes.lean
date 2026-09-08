import Lean

/-!
Checks that the Verso parser and the quotation parsers agree.

Each production appears twice. The first form is document source, which the Verso parser reads. The
second is a quotation, which the parsers in `Lean.Doc.Parser` read. The two trees must be equal once
source info is dropped. Nothing else enforces this agreement, and a break in it shows up far away,
as a view that reads the wrong child.

The second half checks the content accessors by round-tripping values. It writes a decoded value
back out as source, parses it again, and decodes it again, which must reproduce the value.
-/

open Lean Doc Parser Elab Command

/-- Drops source info so that trees built from source and from a quotation can be compared. -/
partial def bare : Syntax → Syntax
  | .node _ k args => .node .none k (args.map bare)
  | .atom _ val => .atom .none val
  | .ident _ raw x _ => .ident .none raw x.eraseMacroScopes []
  | .missing => .missing

/-- Parses `input` as a document and returns its blocks. -/
def parseBlocks (input : String) : IO (Array Syntax) := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do
    throw <| IO.userError s!"parse errors in {input.quote}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  return doc.getVersoBlocks.raw

/-- Parses `input` as a document, which must contain exactly one block. -/
def parseBlock (input : String) : IO Syntax := do
  match ← parseBlocks input with
  | #[b] => return b
  | bs => throw <| IO.userError s!"expected one block from {input.quote}, got {bs.size}"

/-- Parses `input` as a paragraph, which must contain exactly one inline. -/
def parseInline (input : String) : IO Syntax := do
  let b ← parseBlock input
  match BlockView.of ⟨b⟩ with
  | some (.para { content := #[i], .. }) => return i.raw
  | _ => throw <| IO.userError s!"expected one inline from {input.quote}"

/-- Reports whether the tree parsed from `input` matches `quoted`. -/
def sameShape (what input : String) (parsed quoted : Syntax) : IO Unit := do
  if bare parsed == bare quoted then
    IO.println s!"{what}: agree"
  else
    IO.println s!"{what}: DIFFER\n  from source {input.quote}:\n    {parsed}\n  from quotation:\n    {quoted}"

section Shapes

/--
info: text: agree
emph: agree
bold: agree
code: agree
inline math: agree
display math: agree
footnote: agree
link (url): agree
link (ref): agree
image: agree
role (bracketed): agree
role (bare): agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let hi ← `(Parser.inline| $(← mkVersoTextFromRef "hi"):versoText)
  let his : TSyntaxArray ``Parser.inline := #[hi]
  let code ← mkVersoCodeFromRef "x"
  let url ← mkVersoLinkUrlFromRef "u"
  let refName ← mkVersoRefNameFromRef "r"
  let alt ← mkVersoImageAltFromRef "a"
  let fn ← mkVersoRefNameFromRef "f"

  sameShape "text" "hi" (← parseInline "hi") hi.raw
  sameShape "emph" "_hi_" (← parseInline "_hi_")
    (← `(Parser.inline| _$his*_)).raw
  sameShape "bold" "*hi*" (← parseInline "*hi*")
    (← `(Parser.inline| *$his**)).raw
  sameShape "code" "`x`" (← parseInline "`x`")
    (← `(Parser.inline| `$code`)).raw
  sameShape "inline math" "$`x`" (← parseInline "$`x`")
    (← `(Parser.inline| $`$code`)).raw
  sameShape "display math" "$$`x`" (← parseInline "$$`x`")
    (← `(Parser.inline| $$`$code`)).raw
  sameShape "footnote" "[^f]" (← parseInline "[^f]")
    (← `(Parser.inline| [^$fn])).raw
  sameShape "link (url)" "[hi](u)" (← parseInline "[hi](u)")
    (← `(Parser.inline| [$his*]($url))).raw
  sameShape "link (ref)" "[hi][r]" (← parseInline "[hi][r]")
    (← `(Parser.inline| [$his*][$refName])).raw
  sameShape "image" "![a](u)" (← parseInline "![a](u)")
    (← `(Parser.inline| ![$alt]($url))).raw
  sameShape "role (bracketed)" "{r}[hi]" (← parseInline "{r}[hi]")
    (← `(Parser.inline| {r}[$his*])).raw
  sameShape "role (bare)" "{r}`x`" (← parseInline "{r}`x`")
    (← `(Parser.inline| {r}`$code`)).raw

/--
info: para: agree
header: agree
blockquote: agree
unordered list: agree
ordered list: agree
command: agree
link reference: agree
footnote reference: agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let hi ← `(Parser.inline| $(← mkVersoTextFromRef "hi"):versoText)
  let his : TSyntaxArray ``Parser.inline := #[hi]
  -- At the category, a leading `$` opens an antiquotation for the whole block, so a paragraph's
  -- content is spliced with the bracketed form.
  let para ← `(Parser.block| $[$his]*)
  let paras : TSyntaxArray ``Parser.block := #[para]
  let nm ← mkVersoRefNameFromRef "n"
  let u ← mkVersoLinkRefUrlFromRef "u"

  sameShape "para" "hi" (← parseBlock "hi") para.raw
  sameShape "header" "# hi" (← parseBlock "# hi")
    (← `(Parser.block| # $his*)).raw
  sameShape "blockquote" "> hi" (← parseBlock "> hi")
    (← `(Parser.block| > $paras*)).raw
  sameShape "unordered list" "* hi" (← parseBlock "* hi")
    (← `(Parser.block| * $paras*)).raw
  sameShape "ordered list" "1. hi" (← parseBlock "1. hi")
    (← `(Parser.block| 1. $paras*)).raw
  sameShape "command" "{c}" (← parseBlock "{c}")
    (← `(Parser.block| {c})).raw
  sameShape "link reference" "[n]: u" (← parseBlock "[n]: u")
    (← `(Parser.block| [$nm]: $u)).raw
  sameShape "footnote reference" "[^n]: hi" (← parseBlock "[^n]: hi")
    (← `(Parser.block| [^$nm]: $his*)).raw

end Shapes

section Values

/-- Renders inline code containing `value`, using a fence long enough for its content. -/
def renderCode (value : String) : String :=
  let longest := Id.run do
    let mut best := 0
    let mut run := 0
    for c in value.toList do
      if c == '`' then
        run := run + 1
        if run > best then best := run
      else run := 0
    return best
  let fence := "".pushn '`' (longest + 1)
  -- A value that starts or ends with a backtick, or with a space, needs padding so that decoding
  -- strips exactly what rendering added.
  let needsPad := value.startsWith "`" || value.endsWith "`" || value.startsWith " " || value.endsWith " "
  if needsPad then fence ++ " " ++ value ++ " " ++ fence else fence ++ value ++ fence

/-- Renders a code block containing `value` at the given indentation. -/
def renderCodeBlock (indent : Nat) (value : String) : String :=
  let pad := "".pushn ' ' indent
  let body := String.join (value.split '\n' |>.toList.map fun l =>
    if l.isEmpty then "\n" else pad ++ l.copy ++ "\n")
  let body := if value.endsWith "\n" then body.dropEnd 1 else body
  pad ++ "```\n" ++ body ++ pad ++ "```\n"

/-- Escapes `value` so that it parses back as text. -/
def renderText (value : String) : String :=
  String.join (value.toList.map fun c =>
    if c ∈ ['*', '_', '[', ']', '{', '}', '`', '\\', '!', '$'] then "\\" ++ c.toString
    else c.toString)

/-- Checks that writing `value` out as `render` and decoding it again reproduces `value`. -/
def checkValue (what : String) (value : String) (rendered : String)
    (decode : Syntax → Option String) : IO Unit := do
  let b ← parseBlock rendered
  let some got := decode b
    | IO.println s!"{what} {value.quote}: could not decode from {rendered.quote}"
  if got == value then
    IO.println s!"{what} {value.quote}: round-trips"
  else
    IO.println s!"{what} {value.quote}: DIFFERS, got {got.quote} from {rendered.quote}"

def decodeText (b : Syntax) : Option String := do
  let .para { content := #[i], .. } ← BlockView.of ⟨b⟩ | none
  let .text v ← InlineView.of i | none
  some v.getVersoText

def decodeCode (b : Syntax) : Option String := do
  let .para { content, .. } ← BlockView.of ⟨b⟩ | none
  content.findSome? fun i =>
    match InlineView.of i with
    | some (.code v) => some v.getVersoCode
    | _ => none

def decodeCodeBlock (b : Syntax) : Option String := do
  let .codeblock v ← BlockView.of ⟨b⟩ | none
  some v.getVersoCodeBlock

/--
info: text "plain": round-trips
text "star * and underscore _": round-trips
text "backslash \\ and brace {": round-trips
text "brackets [ ] and bang !": round-trips
code "x": round-trips
code "a`b": round-trips
code "a``b": round-trips
code "`lead": round-trips
code "trail`": round-trips
code " spaced ": round-trips
codeblock "one\n": round-trips
codeblock "one\ntwo\n": round-trips
codeblock "one\n\nthree\n": round-trips
codeblock "  indented\n": round-trips
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for v in ["plain", "star * and underscore _", "backslash \\ and brace {",
            "brackets [ ] and bang !"] do
    checkValue "text" v (renderText v) decodeText
  -- A code element needs at least one character of content, so an empty one cannot be written.
  for v in ["x", "a`b", "a``b", "`lead", "trail`", " spaced "] do
    checkValue "code" v ("x" ++ renderCode v) decodeCode
  for v in ["one\n", "one\ntwo\n", "one\n\nthree\n", "  indented\n"] do
    checkValue "codeblock" v (renderCodeBlock 0 v) decodeCodeBlock

end Values

section Encodings

/-!
A view rewrites the `Lean.Doc.Syntax` encoding, which a quotation produced before the parser had
productions of its own, into the encoding the parser produces. The rewritten tree must equal the
tree that the parser reads from the equivalent source.
-/

open scoped Lean.Doc.Syntax

/-- Reports whether the view of `old` produces the tree that the parser reads from `input`. -/
def sameInline (what input : String) (old : TSyntax `inline) : IO Unit := do
  let parsed ← parseInline input
  match InlineView.of old with
  | none => IO.println s!"{what}: NOT A VIEW"
  | some v =>
    if bare v.stx.raw == bare parsed then IO.println s!"{what}: agree"
    else
      IO.println s!"{what}: DIFFER\n  from source {input.quote}:\n    {parsed}\n  \
        rewritten:\n    {v.stx.raw}"

/-- Reports whether the view of `old` produces the tree that the parser reads from `input`. -/
def sameBlock (what input : String) (old : TSyntax `block) : IO Unit := do
  let parsed ← parseBlock input
  match BlockView.of old with
  | none => IO.println s!"{what}: NOT A VIEW"
  | some v =>
    if bare v.stx.raw == bare parsed then IO.println s!"{what}: agree"
    else
      IO.println s!"{what}: DIFFER\n  from source {input.quote}:\n    {parsed}\n  \
        rewritten:\n    {v.stx.raw}"

/--
info: text: agree
emph: agree
bold: agree
code: agree
inline math: agree
display math: agree
link (url): agree
link (ref): agree
image: agree
footnote: agree
role (bracketed): agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  sameInline "text" "hi" (← `(inline| "hi"))
  sameInline "emph" "_hi_" (← `(inline| _["hi"]))
  sameInline "bold" "*hi*" (← `(inline| *["hi"]))
  sameInline "code" "`x`" (← `(inline| code("x")))
  sameInline "inline math" "$`m`" (← `(inline| \math code("m")))
  sameInline "display math" "$$`m`" (← `(inline| \displaymath code("m")))
  sameInline "link (url)" "[hi](u)" (← `(inline| link["hi"]("u")))
  sameInline "link (ref)" "[hi][u]" (← `(inline| link["hi"]["u"]))
  sameInline "image" "![a](u)" (← `(inline| image("a")("u")))
  sameInline "footnote" "[^q]" (← `(inline| footnote("q")))
  sameInline "role (bracketed)" "{r}[hi]" (← `(inline| role{r}["hi"]))

/--
info: para: agree
header: agree
blockquote: agree
unordered list: agree
ordered list: agree
description list: agree
code block: agree
directive: agree
command: agree
link reference: agree
footnote reference: agree
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let hi ← `(block| para["hi"])
  sameBlock "para" "hi" hi
  sameBlock "header" "## hi" (← `(block| header(1){"hi"}))
  sameBlock "blockquote" "> hi" (← `(block| > $hi))
  sameBlock "unordered list" "* hi" (← `(block| ul{* $hi}))
  sameBlock "ordered list" "3. hi" (← `(block| ol(3){* $hi}))
  sameBlock "description list" ": t\n\n  d" (← `(block| dl{: " t" => $(← `(block| para["d"]))}))
  sameBlock "code block" "```\nx\n```" (← `(block| ``` | "x\n" ```))
  sameBlock "directive" "::: d\nhi\n:::" (← `(block| ::: d {$hi}))
  sameBlock "command" "{c}" (← `(block| command{c}))
  sameBlock "link reference" "[n]: u" (← `(block| ["n"]: "u"))
  sameBlock "footnote reference" "[^n]: hi" (← `(block| [^"n"]: "hi"))

/-!
The atoms that the parser writes out, rather than storing in a node, take a position binder in a
quotation. A view reads the atom it needs that way.
-/

/--
info: link brackets: "[" "]"
blockquote marker: ">"
metadata delimiters: "%%%" "%%%"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  match (⟨← parseInline "[hi](u)"⟩ : TSyntax ``Parser.inline) with
  | `(Lean.Doc.Parser.Inline.link| [%$o $_* ]%$c $_:linkTarget) =>
    IO.println s!"link brackets: {o.getAtomVal.quote} {c.getAtomVal.quote}"
  | _ => IO.println "link: no match"
  match (⟨← parseBlock "> hi"⟩ : TSyntax ``Parser.block) with
  | `(Lean.Doc.Parser.Block.blockquote| >%$gt $_*) =>
    IO.println s!"blockquote marker: {gt.getAtomVal.quote}"
  | _ => IO.println "blockquote: no match"
  match (⟨← parseBlock "%%%\n%%%"⟩ : TSyntax ``Parser.block) with
  | `(Lean.Doc.Parser.Block.metadata_block| %%%%$o $_:metadataContents %%%%$c) =>
    IO.println s!"metadata delimiters: {o.getAtomVal.quote} {c.getAtomVal.quote}"
  | _ => IO.println "metadata: no match"

end Encodings
