import Lean

/-!
Checks what the views decode from parser output, and what source information they attach to it.

The parser's round-trip check cannot see these properties. That check confirms that a tree covers
its input. It says nothing about the values read out of the tree, or about whether the language
server can still use the positions.
-/

open Lean Doc Parser Elab Command

/-- Parses `input` as a document containing exactly one block. -/
def theBlock (input : String) : IO Syntax := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do throw <| IO.userError s!"parse errors in {input.quote}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  match doc.getVersoBlocks.raw with
  | #[b] => return b
  | bs => throw <| IO.userError s!"expected one block, got {bs.size}"

/-- Parses `input` as a paragraph containing exactly one inline. -/
def theInline (input : String) : IO Syntax := do
  match BlockView.of ⟨← theBlock input⟩ with
  | some (.para { content := #[i], .. }) => return i.raw
  | _ => throw <| IO.userError s!"expected one inline in {input.quote}"

/-- Names the kind of source info on a literal. -/
def infoKind (stx : Syntax) : String :=
  match stx.getHeadInfo with
  | .original .. => "original"
  | .synthetic _ _ canonical => s!"synthetic (canonical := {canonical})"
  | .none => "none"

/-!
Literals decoded from a docstring that was written in the file keep `.original` source info.

The language server drops term information whose syntax is not `.original`
(`Lean.Server.References` and `SemanticHighlighting` both test for it). Roles such as `name` build
the identifier they report from the literal the view hands them. Weaker info therefore disables
go-to-definition and find-references for names written in docstrings, with no error to point at the
cause.
-/

/--
info: code content: original
image alt content: original
link URL content: original
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let some (.code { content, .. }) := InlineView.of ⟨← theInline "`Nat.add`"⟩
    | throwError "expected code"
  IO.println s!"code content: {infoKind content}"
  let some (.image { alt, target := .url _ _ url _, .. }) := InlineView.of ⟨← theInline "![a](u)"⟩
    | throwError "expected image"
  IO.println s!"image alt content: {infoKind alt}"
  IO.println s!"link URL content: {infoKind url}"

/-!
Text, alternate text, and a URL each decode escape sequences, because the escape character is how a
document writes a character that would otherwise end the content.

A name has no escapes. It is compared for equality with the name that defines it, so the text that
is written is the name. A link reference URL runs to the end of its line, so it has none either.
-/

/--
info: text: "a*b"
image alt: "a]b"
link URL: "u)v"
footnote name: "a-b"
link reference name: "a-b", URL: "u\\)v"
footnote reference name: "a-b"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let some (.text text) := InlineView.of ⟨← theInline "a\\*b"⟩
    | throwError "expected text"
  IO.println s!"text: {text.getVersoText.quote}"
  let some (.image image) := InlineView.of ⟨← theInline "![a\\]b](u\\)v)"⟩
    | throwError "expected image"
  let .url _ _ url _ := image.target | throwError "expected a URL target"
  IO.println s!"image alt: {image.getAlt.quote}"
  IO.println s!"link URL: {url.getVersoLinkUrl.quote}"
  let some (.footnote footnote) := InlineView.of ⟨← theInline "[^a-b]"⟩
    | throwError "expected footnote"
  IO.println s!"footnote name: {footnote.getName.quote}"
  let some (.linkRef linkRef) := BlockView.of ⟨← theBlock "[a-b]: u\\)v"⟩
    | throwError "expected link reference"
  IO.println s!"link reference name: {linkRef.getName.quote}, URL: {linkRef.getUrl.quote}"
  let some (.footnoteRef footnoteRef) := BlockView.of ⟨← theBlock "[^a-b]: text"⟩
    | throwError "expected footnote reference"
  IO.println s!"footnote reference name: {footnoteRef.getName.quote}"

/-!
The range recorded on inline code content delimits the region the decoded value came from. Code that
reparses the content therefore starts the parser at the first character of the value.
-/

/--
info: "`term`": value "term", range covers "term"
"` term `": value "term", range covers "term"
"`  term  `": value " term ", range covers " term "
"` `": value " ", range covers " "
"`a\n b`": value "a\n b", range covers "a\n b"
"` a\n b `": value "a\n b", range covers "a\n b"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["`term`", "` term `", "`  term  `", "` `", "`a\n b`", "` a\n b `"] do
    let some (.code { content, .. }) := InlineView.of ⟨← theInline input⟩
      | throwError "expected code"
    let some b := content.raw.getPos? | throwError "no position"
    let some e := content.raw.getTailPos? | throwError "no tail position"
    IO.println
      s!"{input.quote}: value {content.getVersoCode.quote}, \
       range covers {(String.Pos.Raw.extract input b e).quote}"

/-!
An inline URL decodes its escapes, so a doubled backslash denotes one. It still ends at its closing
parenthesis, so a backslash that escapes that parenthesis leaves the URL unterminated. A link
reference URL has no escapes, so its backslashes stay as written.
-/

/--
info: inline URL: "u\\v"
link reference URL: "u\\\\v"
inline URL ending in a backslash: parse error
link reference URL ending in a backslash: accepted
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let some (.link { target := .url _ _ url _, .. }) := InlineView.of ⟨← theInline "[a](u\\\\v)"⟩
    | throwError "expected link"
  IO.println s!"inline URL: {url.getVersoLinkUrl.quote}"
  let some (.linkRef linkRef) := BlockView.of ⟨← theBlock "[a]: u\\\\v"⟩
    | throwError "expected link reference"
  IO.println s!"link reference URL: {linkRef.getUrl.quote}"
  for (what, input) in [("inline URL", "[a](u\\"), ("link reference URL", "[a]: u\\")] do
    let outcome ← try let _ ← theBlock input; pure "accepted" catch _ => pure "parse error"
    IO.println s!"{what} ending in a backslash: {outcome}"

/-!
A link reference URL ends at the end of its line, so a backslash there cannot pull the following
block into the URL.
-/

/--
info: "[a]: http://x\\\nHello there\n" parses to 2 blocks, errors: 0
"[a]: http://x\\" parses to 1 blocks, errors: 0
URL of "[a]: http://x\\": "http://x\\"
URL of "[a]: http://x\\)y": "http://x\\)y"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["[a]: http://x\\\nHello there\n", "[a]: http://x\\"] do
    let ictx := mkInputContext input "<input>"
    let env : Environment ← mkEmptyEnvironment
    let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
    IO.println
      s!"{input.quote} parses to {(⟨s.stxStack.back⟩ : VersoDocument).getVersoBlocks.size} \
        blocks, errors: {s.allErrors.size}"
  for input in ["[a]: http://x\\", "[a]: http://x\\)y"] do
    let some (.linkRef linkRef) := BlockView.of ⟨← theBlock input⟩
      | throwError "expected a link reference"
    IO.println s!"URL of {input.quote}: {linkRef.getUrl.quote}"

/-!
An argument value written as a numeral denotes a natural number. The parser rejects a literal that
is not a natural number.
-/

/--
info: (width := 3) reads as some 3
(width := 1.5) reads as none
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for value in ["3", "1.5"] do
    let some (.directive { args, .. }) :=
        BlockView.of ⟨← theBlock s!":::note (width := {value})\ncontent\n:::\n"⟩
      | throwError "expected a directive"
    let some (.named _ _ _ _ v) := ArgView.of args[0]!
      | throwError "expected a named argument"
    IO.println s!"(width := {value}) reads as {repr ((ArgValView.of v).bind fun
      | .num _ n => some n
      | _ => none)}"

/-!
The parser leaves every node without source info of its own, so the content node of an empty code
block has no position in the tree. The view supplies one as a zero-width string at the start of the
closing fence. A code block expander can then report its diagnostics at the block itself.
-/

/--
info: parsed empty content has its own position: false
view content is positioned: true
view content position is the closing fence's start, zero-width: true
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let blk ← theBlock "```lean\n```\n"
  IO.println s!"parsed empty content has its own position: {(blk.getArg 2).getPos?.isSome}"
  let some (.codeblock { content, closeFence, .. }) := BlockView.of ⟨blk⟩
    | throwError "expected a code block"
  IO.println s!"view content is positioned: {(content.raw.getPos? (canonicalOnly := true)).isSome}"
  let atFence :=
    content.raw.getPos? == closeFence.raw.getPos? &&
    content.raw.getTailPos? == closeFence.raw.getPos?
  IO.println s!"view content position is the closing fence's start, zero-width: {atFence}"

/-!
A code block with no content lines has empty contents, and one with a single blank line contains
one newline.
-/

/--
info: empty: ""
one blank line: "\n"
one line: "x\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for (what, input) in [("empty", "```\n```\n"), ("one blank line", "```\n\n```\n"),
                        ("one line", "```\nx\n```\n")] do
    let some (.codeblock codeblock) := BlockView.of ⟨← theBlock input⟩
      | throwError "expected code block"
    IO.println s!"{what}: {codeblock.getVersoCodeBlock.quote}"

/-!
The contents of a code block are one token per source line, which `getVersoCodeBlock` reads as a
single value.
-/

/--
info: lines: ["a\n", "b\n", "\n", "c\n"]
whole: "a\nb\n\nc\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let some (.codeblock codeblock) := BlockView.of ⟨← theBlock "```\na\nb\n\nc\n```\n"⟩
    | throwError "expected a code block"
  let lines := codeblock.content.raw[0].getArgs.map fun l => TSyntax.getVersoCodeLine ⟨l⟩
  IO.println s!"lines: {lines.toList.map (·.quote)}"
  IO.println s!"whole: {codeblock.getVersoCodeBlock.quote}"


/-!
An extension reparses the value in a literal content token, so content with no position of its own
is parsed from that value. Inline code and code blocks read their contents through the accessor for
the kind of token each uses.
-/

/-- Strips the source positions from `stx`, as a macro-generated document has none. -/
partial def unpositioned : Syntax → Syntax
  | .node _ kind args => .node .none kind (args.map unpositioned)
  | .atom _ s => .atom .none s
  | .ident _ s x pre => .ident .none s x pre
  | .missing => .missing

/--
info: inline code: (num "42")
code block: (num "42")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let code ← `(Parser.inline| `$(← mkVersoCodeFromRef "42")`)
  let some (.code { content, .. }) := InlineView.of ⟨unpositioned code.raw⟩
    | throwError "expected inline code"
  IO.println s!"inline code: {← parseVersoCode (categoryParserFn `term) content}"
  let block ← `(Parser.block| ```$(← mkVersoCodeBlockFromRef "42"):versoCodeBlock```)
  let some (.codeblock { content, .. }) := BlockView.of ⟨unpositioned block.raw⟩
    | throwError "expected a code block"
  IO.println s!"code block: {← parseVersoCodeBlock (categoryParserFn `term) content}"

/-!
Recovery from an unclosed inline code element keeps the rest of the line as the element's content
and records the line's newline in the tree, so this recovered parse reprints its input. This is a
property of this recovery path: recovery in general leaves the input it skips uncovered, as the
parser for Lean itself does.
-/

/--
info: recovered parse reprints its input: true
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let input := "before `code\nafter\n"
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  if s.allErrors.isEmpty then throwError "expected a recovered error"
  let reprinted := s.stxStack.back.reprint.getD ""
  unless reprinted == input do
    IO.println s!"reprint {reprinted.quote} differs from input {input.quote}"
  IO.println s!"recovered parse reprints its input: {reprinted == input}"

/-!
Between multiline arguments, the run through the last newline belongs to the preceding token's
trailing whitespace, and the indentation of the line where the next argument resumes belongs to
that argument's first token as leading whitespace.
-/

/-- The text, leading, and trailing of each token in `stx`, in order. -/
partial def tokenWhitespace (stx : Syntax) : Array (String × String × String) :=
  match stx with
  | .node _ _ args => args.foldl (fun acc a => acc ++ tokenWhitespace a) #[]
  | .atom (.original lead _ trail _) val =>
    #[(val, String.Pos.Raw.extract lead.str lead.startPos lead.stopPos,
       String.Pos.Raw.extract trail.str trail.startPos trail.stopPos)]
  | .ident (.original lead _ trail _) raw _ _ =>
    #[(raw.toString, String.Pos.Raw.extract lead.str lead.startPos lead.stopPos,
       String.Pos.Raw.extract trail.str trail.startPos trail.stopPos)]
  | _ => #[]

/--
info: "foo": leading " ", trailing ""
"a1": leading " ", trailing "\n"
"a2": leading " ", trailing ""
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let input := " foo a1\n a2"
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := (nameAndArgsFn (multiline := some 1)).run ictx {env, options := {}}
    (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do throwError "parse errors in {input.quote}"
  for i in [0:s.stxStack.size] do
    for (t, l, tr) in tokenWhitespace (s.stxStack.get! i) do
      IO.println s!"{t.quote}: leading {l.quote}, trailing {tr.quote}"

/-!
Each line of a code block is one token. The token's leading whitespace is the code block's
indentation, and indentation past that is part of the token's content. A blank line that is shorter
than the code block's indentation contributes all of its spaces as leading whitespace.
-/

/-- The leading whitespace and the content of each code block line token in `stx`, in order. -/
partial def codeBlockLines (stx : Syntax) : Array (String × String) :=
  if stx.isOfKind versoCodeLineKind then
    match stx.getHeadInfo, Syntax.isLit? versoCodeLineKind stx with
    | .original lead .., some content =>
      #[(String.Pos.Raw.extract lead.str lead.startPos lead.stopPos, content)]
    | _, _ => #[]
  else stx.getArgs.foldl (fun acc a => acc ++ codeBlockLines a) #[]

/--
info: unindented:
  leading "", content "a\n"
  leading "", content "  b\n"
indented by two:
  leading "  ", content "a\n"
  leading "  ", content "  b\n"
blank line with no spaces:
  leading "  ", content "a\n"
  leading "", content "\n"
  leading "  ", content "b\n"
blank line shorter than the indentation:
  leading "  ", content "a\n"
  leading " ", content "\n"
  leading "  ", content "b\n"
blank line longer than the indentation:
  leading "  ", content "a\n"
  leading "  ", content "  \n"
  leading "  ", content "b\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for (what, input) in
      [("unindented", "```\na\n  b\n```\n"),
       ("indented by two", "* x\n\n  ```\n  a\n    b\n  ```\n"),
       ("blank line with no spaces", "* x\n\n  ```\n  a\n\n  b\n  ```\n"),
       ("blank line shorter than the indentation", "* x\n\n  ```\n  a\n \n  b\n  ```\n"),
       ("blank line longer than the indentation", "* x\n\n  ```\n  a\n    \n  b\n  ```\n")] do
    IO.println s!"{what}:"
    for (lead, content) in codeBlockLines (← theBlock input) do
      IO.println s!"  leading {lead.quote}, content {content.quote}"
