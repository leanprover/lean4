import Lean

/-!
Checks that a literal content token built for a quotation's document reads back exactly the value it
was built from.
-/

open Lean Doc Parser Elab Command

/-- Values that interact with the escaping mechanism's encodings. -/
def awkward : List String :=
  ["", "x", "\\", "a\\b", "\\\\", "a\\\\b", "\\n", "]", "\"", "\n", "a\nb", " ", "  ", "   ",
   " x ", " x", "x ", "  x  ", "`", "``", "` `", "\t"]

/-- Reports every value that did not survive a round trip through `f`. -/
def report (what : String) (f : String → CommandElabM String) : CommandElabM Unit := do
  let mut bad := #[]
  for v in awkward do
    let v' ← f v
    unless v' == v do bad := bad.push s!"{v.quote} became {v'.quote}"
  if bad.isEmpty then
    IO.println s!"{what}: all {awkward.length} values preserved"
  else
    IO.println s!"{what}: {bad.size} of {awkward.length} values changed"
    for b in bad do IO.println s!"  {b}"

/-!
Everywhere a quotation can write content, the value written is the value read back.
-/

/--
info: text: all 22 values preserved
inline code: all 22 values preserved
inline math: all 22 values preserved
display math: all 22 values preserved
image alt: all 22 values preserved
footnote name: all 22 values preserved
link URL: all 22 values preserved
link reference name: all 22 values preserved
link reference URL: all 22 values preserved
footnote name in a reference: all 22 values preserved
code block: all 22 values preserved
code block with a language: all 22 values preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  report "text" fun v => do
    let some (.text view) :=
        InlineView.of (← `(Parser.inline| $(← mkVersoTextFromRef v):versoText))
      | throwError "expected text"
    return view.getVersoText
  report "inline code" fun v => do
    let some (.code view) := InlineView.of (← `(Parser.inline| `$(← mkVersoCodeFromRef v)`))
      | throwError "expected code"
    return view.getVersoCode
  report "inline math" fun v => do
    let some (.math view) := InlineView.of (← `(Parser.inline| $`$(← mkVersoCodeFromRef v)`))
      | throwError "expected math"
    return view.getVersoCode
  report "display math" fun v => do
    let some (.math view) := InlineView.of (← `(Parser.inline| $$`$(← mkVersoCodeFromRef v)`))
      | throwError "expected math"
    return view.getVersoCode
  report "image alt" fun v => do
    let some (.image view) :=
        InlineView.of
          (← `(Parser.inline| ![$(← mkVersoImageAltFromRef v)]($(← mkVersoLinkUrlFromRef "u"))))
      | throwError "expected image"
    return view.getAlt
  report "footnote name" fun v => do
    let some (.footnote view) :=
        InlineView.of (← `(Parser.inline| [^$(← mkVersoRefNameFromRef v)]))
      | throwError "expected footnote"
    return view.getName
  report "link URL" fun v => do
    let some (.link { target := .url _ _ url _, .. }) :=
        InlineView.of (← `(Parser.inline| []($(← mkVersoLinkUrlFromRef v))))
      | throwError "expected link"
    return url.getVersoLinkUrl
  report "link reference name" fun v => do
    let some (.linkRef view) :=
        BlockView.of
          (← `(Parser.block| [$(← mkVersoRefNameFromRef v)]: $(← mkVersoLinkRefUrlFromRef "u")))
      | throwError "expected link reference"
    return view.getName
  report "link reference URL" fun v => do
    let some (.linkRef view) :=
        BlockView.of
          (← `(Parser.block| [$(← mkVersoRefNameFromRef "n")]: $(← mkVersoLinkRefUrlFromRef v)))
      | throwError "expected link reference"
    return view.getUrl
  report "footnote name in a reference" fun v => do
    let text : TSyntaxArray ``Parser.inline :=
      #[← `(Parser.inline| $(← mkVersoTextFromRef "t"):versoText)]
    let some (.footnoteRef view) :=
        BlockView.of (← `(Parser.block| [^$(← mkVersoRefNameFromRef v)]: $[$text]*))
      | throwError "expected footnote reference"
    return view.getName
  report "code block" fun v => do
    let some (.codeblock view) :=
        BlockView.of (← `(Parser.block| ```$(← mkVersoCodeBlockFromRef v):versoCodeBlock```))
      | throwError "expected code block"
    return view.getVersoCodeBlock
  report "code block with a language" fun v => do
    let some (.codeblock view) :=
        BlockView.of (← `(Parser.block| ```lean $(← mkVersoCodeBlockFromRef v):versoCodeBlock```))
      | throwError "expected code block"
    return view.getVersoCodeBlock

/-!
Content tokens that the parser produces have the same values as the ones a quotation produces, so a
consumer reading a value cannot tell where the document came from.
-/

/-- Parses `input` as a document containing exactly one block. -/
def oneBlock (input : String) : IO Syntax := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do throw <| IO.userError s!"parse errors in {input.quote}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  match doc.getVersoBlocks.raw with
  | #[b] => return b
  | bs => throw <| IO.userError s!"expected one block, got {bs.size}"

/-- Reads the code of a paragraph with a single inline code element. -/
def parsedCode (input : String) : CommandElabM String := do
  let some (.para { content := #[i], .. }) := BlockView.of ⟨← oneBlock input⟩ | throwError "expected a paragraph"
  let some (.code view) := InlineView.of i | throwError "expected code"
  return view.getVersoCode

/-- Reads the code of a quotation with a single inline code element. -/
def quotedCode (value : String) : CommandElabM String := do
  let some (.code view) := InlineView.of (← `(Parser.inline| `$(← mkVersoCodeFromRef value)`))
    | throwError "expected code"
  return view.getVersoCode

/--
info: "`term`" parses to "term", which a quotation also reads as "term"
"` term `" parses to "term", which a quotation also reads as "term"
"`  term  `" parses to " term ", which a quotation also reads as " term "
"`a\\b`" parses to "a\\b", which a quotation also reads as "a\\b"
"` `" parses to " ", which a quotation also reads as " "
"``x``" parses to "x", which a quotation also reads as "x"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for (source, value) in
      [("`term`", "term"), ("` term `", "term"), ("`  term  `", " term "), ("`a\\b`", "a\\b"),
       ("` `", " "), ("``x``", "x")] do
    let parsed ← parsedCode source
    unless parsed == value do
      throwError "{source} parses to {parsed.quote}, expected {value.quote}"
    let quoted ← quotedCode value
    unless quoted == value do
      throwError "a quotation of {value.quote} reads as {quoted.quote}"
    IO.println
      s!"{source.quote} parses to {value.quote}, which a quotation also reads as {quoted.quote}"

/-!
The `of` functions do not depend on where each part of a tree came from. A link whose target was
built separately from its surrounding element is viewed the same way.
-/

/-- Describes a link target compactly. -/
def describeTarget : LinkTargetView → String
  | .url _ _ u _ => s!"url({u.getVersoLinkUrl.quote})"
  | .ref _ _ n _ => s!"ref({n.getVersoRefName.quote})"

/-- The syntax a link target view was constructed from. -/
def targetSyntax : LinkTargetView → Syntax
  | .url stx .. | .ref stx .. => stx.raw

/-- Parses `input` as a paragraph with a single inline element. -/
def oneInline (input : String) : CommandElabM Syntax := do
  let some (.para { content := #[i], .. }) := BlockView.of ⟨← oneBlock input⟩ | throwError "expected a paragraph"
  return i.raw

/-- Replaces a link's target, which the parser and quotations both place in the same position. -/
def withTarget (link : Syntax) (target : LinkTargetView) : Syntax :=
  link.setArg 3 (targetSyntax target)

/--
info: parser-built link with a quotation-built target: url("http://x")
quotation-built link with a parser-built target: url("http://x")
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  let parserLink ← oneInline "[a](http://x)"
  let quotedText : TSyntaxArray ``Parser.inline :=
    #[← `(Parser.inline| $(← mkVersoTextFromRef "a"):versoText)]
  let quotedLink :=
    (← `(Parser.inline| [$[$quotedText]*]($(← mkVersoLinkUrlFromRef "http://x")))).raw
  let some (.link { target := parserTarget, .. }) := InlineView.of ⟨parserLink⟩
    | throwError "expected a link"
  let some (.link { target := quotedTarget, .. }) := InlineView.of ⟨quotedLink⟩
    | throwError "expected a link"
  let some (.link { target := t, .. }) := InlineView.of ⟨withTarget parserLink quotedTarget⟩
    | throwError "no view for a parser-built link with a quotation-built target"
  IO.println s!"parser-built link with a quotation-built target: {describeTarget t}"
  let some (.link { target := t, .. }) := InlineView.of ⟨withTarget quotedLink parserTarget⟩
    | throwError "no view for a quotation-built link with a parser-built target"
  IO.println s!"quotation-built link with a parser-built target: {describeTarget t}"
