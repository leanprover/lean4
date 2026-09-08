import Lean

/-!
Checks that formatting a document produces Verso that parses back to the same document.

The formatter renders canonically, so its output may differ from what was written. It must still
leave the meaning of the document unchanged.
-/

open Lean Doc Parser Elab Command
open scoped Lean.Doc.Syntax

/-- Parses `input` as a document and returns its blocks. -/
def blocksOf (input : String) : IO (TSyntaxArray ``Parser.block) := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  unless s.allErrors.isEmpty do throw <| IO.userError s!"parse errors in {input.quote}"
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  return doc.getVersoBlocks

/-- Describes a document in enough detail to notice a construct changing into a different one. -/
partial def shape (stx : TSyntax ``Parser.block) : String :=
  match BlockView.of stx with
  | some (.para v) =>
    let inls := v.content
    -- The block break writes the newline that ends the last line of a paragraph.
    let inls := if inls.back?.any isLinebreak then inls.pop else inls
    "para[" ++ " ".intercalate (inls.map (inlineShape ·)).toList ++ "]"
  | some (.metadata ..) => "metadata"
  | some (.header v) =>
    s!"header({v.level})[" ++ " ".intercalate (v.content.map (inlineShape ·)).toList ++ "]"
  | some (.ul v) => "ul[" ++ " ".intercalate (v.items.map (unorderedItemShape ·)).toList ++ "]"
  | some (.ol v) =>
    s!"ol({v.start})[" ++ " ".intercalate (v.items.map (orderedItemShape ·)).toList ++ "]"
  | some (.dl v) => "dl[" ++ " ".intercalate (v.items.map (descShape ·)).toList ++ "]"
  | some (.blockquote v) =>
    "quote[" ++ " ".intercalate (v.content.map (shape ·)).toList ++ "]"
  | some (.directive v) =>
    s!"directive({v.name.getId.eraseMacroScopes})[" ++
      " ".intercalate (v.content.map (shape ·)).toList ++ "]"
  | some (.codeblock v) =>
    let name := v.name?.map (·.getId.eraseMacroScopes) |>.getD .anonymous
    s!"codeblock({name}, {v.getVersoCodeBlock.quote})"
  | some _ => "block"
  | none => s!"<not a block: {stx.raw.getKind}>"
where
  unorderedItemShape (item : UnorderedListItemView) : String :=
    "item[" ++ " ".intercalate (item.contents.map (shape ·)).toList ++ "]"
  orderedItemShape (item : OrderedListItemView) : String :=
    "item[" ++ " ".intercalate (item.contents.map (shape ·)).toList ++ "]"
  descShape (item : DescItemView) : String :=
    "desc[" ++ " ".intercalate (item.term.map (inlineShape ·)).toList ++ " | " ++
      " ".intercalate (item.desc.map (shape ·)).toList ++ "]"
  isLinebreak (i : TSyntax ``Parser.inline) : Bool :=
    match InlineView.of i with
    | some (.linebreak ..) => true
    | _ => false
  inlineShape (i : TSyntax ``Parser.inline) : String :=
    match InlineView.of i with
    | some (.text v) => s!"text({v.getVersoText.quote})"
    | some (.code v) => s!"code({v.getVersoCode.quote})"
    | some (.link ..) => "link"
    | some (.footnote v) => s!"footnote({v.getName.quote})"
    | some (.image ..) => "image"
    | some (.role v) =>
      s!"role({v.name.getId.eraseMacroScopes})[" ++
        " ".intercalate (v.content.map (inlineShape ·)).toList ++ "]"
    | some (.emph v) =>
      "emph[" ++ " ".intercalate (v.content.map (inlineShape ·)).toList ++ "]"
    | some (.bold v) =>
      "bold[" ++ " ".intercalate (v.content.map (inlineShape ·)).toList ++ "]"
    | some (.math v) =>
      let m := match v.mode with | .inline => "inline" | .display => "display"
      s!"math({m}, {v.getVersoCode.quote})"
    | some (.linebreak ..) => "linebreak"
    | none => "<not an inline>"

/-- Formats `input`, parses the result, and reports the shape of both. -/
def roundTrip (input : String) : IO Unit := do
  let before := (← blocksOf input).map shape
  let formatted := versoDocumentToString (← blocksOf input)
  let after? ← try pure (some ((← blocksOf formatted).map shape)) catch _ => pure none
  match after? with
  | none =>
    IO.println s!"{input.quote}: REPARSE FAILED\n  formatted: {formatted.quote}"
  | some after =>
    if before == after then
      IO.println s!"{input.quote}: preserved"
    else
      IO.println s!"{input.quote}: CHANGED\n  before: {before}\n  after:  {after}\n  formatted: {formatted.quote}"

/-- Formats `input` and prints the exact result, checking that it reads back the same. -/
def exactFormat (input : String) : IO Unit := do
  let blocks ← blocksOf input
  let formatted := versoDocumentToString blocks
  let same ← try pure ((← blocksOf formatted).map shape == blocks.map shape) catch _ => pure false
  IO.println s!"{input.quote} => {formatted.quote}{if same then "" else " (CHANGED)"}"

/-- Formats a block that was built rather than parsed, and reports what the result parses as. -/
def roundTripBlock (stx : TSyntax ``Parser.block) : IO Unit := do
  let formatted := versoSyntaxToString stx.raw
  IO.println s!"{shape stx}\n  formatted: {formatted.quote}"
  let after? ← try pure (some ((← blocksOf formatted).map shape)) catch _ => pure none
  match after? with
  | none => IO.println "  REPARSE FAILED"
  | some after => IO.println s!"  parses as: {after}"

/-- Formats blocks that were built rather than parsed, and reports what the result parses as. -/
def roundTripDocument (blocks : TSyntaxArray ``Parser.block) : IO Unit := do
  let formatted := versoDocumentToString blocks
  IO.println s!"{" ".intercalate (blocks.map (shape ·)).toList}\n  formatted: {formatted.quote}"
  let after? ← try pure (some ((← blocksOf formatted).map shape)) catch _ => pure none
  match after? with
  | none => IO.println "  REPARSE FAILED"
  | some after => IO.println s!"  parses as: {after}"

/-!
A role whose content is a single self-delimiting element prints without brackets, but only where
that is unambiguous. A link and a footnote both open with `[`, which the role parser reads as the
opening bracket of the role's content.
-/

/--
info: "{lit}`x`": preserved
"{lit}[`x`]": preserved
"{lit}[[a](u)]": preserved
"{lit}[[^f]]": preserved
"{lit}[![a](u)]": preserved
"{lit}[a *b*]": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["{lit}`x`", "{lit}[`x`]", "{lit}[[a](u)]", "{lit}[[^f]]", "{lit}[![a](u)]",
                "{lit}[a *b*]"] do
    roundTrip input

/-!
The brackets also stay where the element after the role would run into the role's content. The
parser reads two code elements written next to each other as one longer backtick delimiter.
-/

/--
info: "{lit}[`x`]`y`": preserved
"{lit}[`x`] `y`": preserved
"{lit}[*x*]*y*": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["{lit}[`x`]`y`", "{lit}[`x`] `y`", "{lit}[*x*]*y*"] do
    roundTrip input

/-!
Content prints in a form that reads back as the same content. Text re-escapes the characters that
would otherwise start markup, and inline code gets delimiters long enough for its contents.
-/

/--
info: "a \\`x\\` b": preserved
"a \\*x\\* b": preserved
"a \\\\ b": preserved
"Text `` `x `` here": preserved
"`` ` ``": preserved
"`x`": preserved
"a \\[b\\] c": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["a \\`x\\` b", "a \\*x\\* b", "a \\\\ b", "Text `` `x `` here", "`` ` ``", "`x`",
                "a \\[b\\] c"] do
    roundTrip input

/-!
Where a block starts, the formatter escapes text that begins with a character that would open a
different kind of block, so a paragraph stays a paragraph.
-/

/--
info: "\\# not a header": preserved
"\\> not a quote": preserved
"\\- not a bullet": preserved
"\\+ not a bullet": preserved
"\\1. not a list": preserved
"\\: not a description": preserved
"\\%%% not metadata": preserved
"a - b": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["\\# not a header", "\\> not a quote", "\\- not a bullet", "\\+ not a bullet",
                "\\1. not a list", "\\: not a description", "\\%%% not metadata", "a - b"] do
    roundTrip input

/-!
A leading character gets an escape only where the parser would read the line as the opener of a
different kind of block:

* A digit, only when digits, `.` or `)`, and a space or the end of the line follow it.
* A bullet or a colon, only with its trailing space. A bullet also gets one at the end of the line.
* A leading `#`, always. A header without its space is an error, so the escape is always needed.
-/

/--
info: "2023 was a year" => "2023 was a year\n"
"1.5 million" => "1.5 million\n"
"10x speedup" => "10x speedup\n"
"-x is negated" => "-x is negated\n"
"+1 for that" => "+1 for that\n"
":: colons" => ":: colons\n"
":" => ":\n"
"%50 done" => "%50 done\n"
"2." => "\\2.\n"
"-" => "\\-\n"
"\\1. a list" => "\\1. a list\n"
"\\12) also a list" => "\\12) also a list\n"
"\\- a bullet" => "\\- a bullet\n"
"\\: a description" => "\\: a description\n"
"\\::: a directive" => "\\::: a directive\n"
"\\%%% metadata" => "\\%%% metadata\n"
"\\#1 hit" => "\\#1 hit\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["2023 was a year", "1.5 million", "10x speedup", "-x is negated", "+1 for that",
                ":: colons", ":", "%50 done", "2.", "-", "\\1. a list", "\\12) also a list",
                "\\- a bullet", "\\: a description", "\\::: a directive", "\\%%% metadata",
                "\\#1 hit"] do
    exactFormat input

/-!
Every kind of block is printed as Verso, and an indented block closes at the column it opened at.
-/

/--
info: "```\nx\n```\n": preserved
"```lean\nx\n```\n": preserved
"* item\n\n  ```lean\n  x\n  ```\n": preserved
": term\n\n  Description\n": preserved
"[r]: http://x\n": preserved
"[^f]: note\n": preserved
"Hello\n\n[r]: http://x\n\nSee [a][r]\n": preserved
"> a\n>\n> b\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["```\nx\n```\n", "```lean\nx\n```\n", "* item\n\n  ```lean\n  x\n  ```\n",
                ": term\n\n  Description\n", "[r]: http://x\n", "[^f]: note\n",
                "Hello\n\n[r]: http://x\n\nSee [a][r]\n", "> a\n>\n> b\n"] do
    roundTrip input

/-!
A role keeps its brackets when the printed content ends in the delimiter that the next element
opens with. The rule applies whether or not the source wrote the content with brackets of its own.
-/

/--
info: "{a}[{b}[`x`]]`y`": preserved
"{a}[{b}[`x`]] `y`": preserved
"{a}[{b}[*x*]]*y*": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["{a}[{b}[`x`]]`y`", "{a}[{b}[`x`]] `y`", "{a}[{b}[*x*]]*y*"] do
    roundTrip input

/-!
A role also loses its brackets where its content ends in the delimiter that closes the emph or bold
element around it. The parser reads a closing run as exactly as many characters as the opening run
of the element it closes.
-/

/--
info: "**{role}[*b*]**": preserved
"**a {role}[*b*]**": preserved
"__{role}[_e_]__": preserved
"***{role}[**b**]***": preserved
"**{role}[{r}[*b*]]**": preserved
"**{role}[*b*]*c***": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["**{role}[*b*]**", "**a {role}[*b*]**", "__{role}[_e_]__", "***{role}[**b**]***",
                "**{role}[{r}[*b*]]**", "**{role}[*b*]*c***"] do
    roundTrip input

/-!
Content that a document uses as written also prints as written, so the escapes that let it include
its delimiter survive a round trip.
-/

/--
info: "![a\\]b](u\\)v)": preserved
"[a-b]: u\\)v": preserved
"[^a-b]": preserved
"[hi][a-b]": preserved
"[a]: C:\\path": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["![a\\]b](u\\)v)", "[a-b]: u\\)v", "[^a-b]", "[hi][a-b]", "[a]: C:\\path"] do
    roundTrip input

/-!
Every item of a list prints at the indentation of the list it belongs to, so a list nested in an
item stays nested. The space after the colon of a description list item is part of the term it
introduces.
-/

/--
info: "* a\n  * b\n  * c\n": preserved
"* a\n* b\n": preserved
"1. a\n   1. b\n   1. c\n": preserved
"1. a\n2. b\n": preserved
": t\n\n  * a\n  * b\n\n: t2\n\n  d\n": preserved
":  t\n\n  d\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["* a\n  * b\n  * c\n", "* a\n* b\n", "1. a\n   1. b\n   1. c\n", "1. a\n2. b\n",
                ": t\n\n  * a\n  * b\n\n: t2\n\n  d\n", ":  t\n\n  d\n"] do
    roundTrip input

/-!
An item's contents are indented past its bullet. That is the indentation the parser requires for
contents that belong to the item.
-/

/--
info: "10. a\n    * b\n": preserved
"9. a\n   * b\n10. c\n    * d\n": preserved
"100. a\n     * b\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["10. a\n    * b\n", "9. a\n   * b\n10. c\n    * d\n", "100. a\n     * b\n"] do
    roundTrip input

/-!
The parser reads two lists of the same kind that stand next to each other as one list, unless their
indicators differ. Neighboring lists therefore alternate between the two indicators of their
kind.
-/

/--
info: "* a\n\n\n * b\n": preserved
"1. a\n\n 2. b\n": preserved
"* a\n\n\n * b\n\n\n  * c\n": preserved
"* a\n\n1. b\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["* a\n\n\n * b\n", "1. a\n\n 2. b\n", "* a\n\n\n * b\n\n\n  * c\n",
                "* a\n\n1. b\n"] do
    roundTrip input

/-!
The contents of a code block print as whole lines, so the closing fence stands at the start of a
line. The rule applies to contents that were built as well as to contents that were parsed.
-/

/--
info: codeblock([anonymous], "plain")
  formatted: "```\nplain\n```\n"
  parses as: #[codeblock([anonymous], "plain\n")]
codeblock([anonymous], "")
  formatted: "```\n```\n"
  parses as: #[codeblock([anonymous], "")]
codeblock([anonymous], "two\nlines")
  formatted: "```\ntwo\nlines\n```\n"
  parses as: #[codeblock([anonymous], "two\nlines\n")]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  roundTripBlock (← `(block| ``` | "plain" ```))
  roundTripBlock (← `(block| ``` | "" ```))
  roundTripBlock (← `(block| ``` | "two\nlines" ```))

/-!
A metadata block describes the document or a section of it, so the parser recognizes it only at the
top level. After a list or a blockquote, one attaches as the block's sibling. Inside a directive,
where the delimiters leave no other reading, it is a parse error.
-/

/--
info: "* a\n\n%%%\nx := 1\n%%%\n": preserved
"> a\n\n%%%\nx := 1\n%%%\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["* a\n\n%%%\nx := 1\n%%%\n", "> a\n\n%%%\nx := 1\n%%%\n"] do
    roundTrip input

/--
error: parse errors in "::: d\n%%%\nx := 1\n%%%\n:::\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  roundTrip "::: d\n%%%\nx := 1\n%%%\n:::\n"

/-!
Inline code with no content prints as a single space, which is the shortest content the syntax
admits.
-/

/--
info: para[code("")]
  formatted: "` `\n"
  parses as: #[para[code(" ")]]
para[text("a") code("") text("b")]
  formatted: "a` `b\n"
  parses as: #[para[text("a") code(" ") text("b")]]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  roundTripBlock (← `(block| para[code("")]))
  roundTripBlock (← `(block| para["a" code("") "b"]))

/-!
The document formatter renders a metadata block as Verso, so a document that contains one reads
back as the same document. Its delimiters are on their own lines.
-/

/--
info: "# Title\n\n%%%\nauthors := \"me\"\n%%%\n"
  formatted: "# Title\n\n%%%\nauthors := \"me\"\n%%%\n"
  parses as: #[header(0)[text("Title")], metadata] (same)
"%%%\nauthors := \"me\"\n%%%\n\ntext\n"
  formatted: "%%%\nauthors := \"me\"\n%%%\n\ntext\n"
  parses as: #[metadata, para[text("text")]] (same)
"text\n\n%%%\nx := 1\n%%%\n"
  formatted: "text\n\n%%%\nx := 1\n%%%\n"
  parses as: #[para[text("text")], metadata] (same)
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["# Title\n\n%%%\nauthors := \"me\"\n%%%\n",
                "%%%\nauthors := \"me\"\n%%%\n\ntext\n",
                "text\n\n%%%\nx := 1\n%%%\n"] do
    let blocks ← blocksOf input
    let rendered :=
      toString (← liftCoreM <| PrettyPrinter.format document.formatter
        (.node .none ``Parser.document #[mkNullNode (blocks.map (·.raw))]))
    IO.println s!"{input.quote}\n  formatted: {rendered.quote}"
    let after? ← try pure (some ((← blocksOf rendered).map shape)) catch _ => pure none
    match after? with
    | none => IO.println "  REPARSE FAILED"
    | some after =>
      let same := after == blocks.map shape
      IO.println s!"  parses as: {after}{if same then " (same)" else " (CHANGED)"}"

/-!
A metadata block that was built rather than parsed has no source text, so its delimiters and its
contents print from the syntax. The delimiters are on their own lines there too, and the
spacing of the contents is the spacing that printing the syntax gives.
-/

/--
info: metadata
  formatted: "%%%\nfoo  :=  1 \n%%%\n"
  parses as: #[metadata]
metadata
  formatted: "%%%\n%%%\n"
  parses as: #[metadata]
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  roundTripBlock (← `(block| %%% foo := 1 %%%))
  roundTripBlock (← `(block| %%% %%%))

/-- Formats `input` and reports the text exactly. -/
def showFormatted (input : String) : CommandElabM Unit := do
  IO.println s!"{input.quote} => {(versoDocumentToString (← blocksOf input)).quote}"

/-!
An item with no contents prints its bullet alone, as an empty block quotation prints its marker
alone. Neither leaves a space at the end of the line.
-/

/--
info: "*   \n" => "*\n"
"1.\n" => "1.\n"
"> \n" => ">\n"
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["*   \n", "1.\n", "> \n"] do
    showFormatted input

/-!
A block that the parser reads only at the start of a line follows its list item's bullet on the
next line, indented to the item's contents.
-/

/--
info: "*\n  [r]: u\n": preserved
"*\n  [^f]: t\n": preserved
"1.\n   # h\n": preserved
"* a\n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["*\n  [r]: u\n", "*\n  [^f]: t\n", "1.\n   # h\n", "* a\n"] do
    roundTrip input

/-!
Text that the parser would read as a block opener keeps its escape. The parser skips spaces before
an opener and rejects a tab where one may begin, so neither hides an opener from the formatter.

A paragraph whose text is written with an escape is content, even where the escape stands before a
space. The parser judges a paragraph by the text as it was written, and rejects one that is nothing
but whitespace, so the escape stays.
-/

/--
info: "\\ - x\n": preserved
"\\ > q\n": preserved
"\\ 1. a\n": preserved
"\\ ::: d\n": preserved
"\\ : t\n": preserved
"\\\t- i\n": preserved
"\\ \n": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  for input in ["\\ - x\n", "\\ > q\n", "\\ 1. a\n", "\\ ::: d\n", "\\ : t\n", "\\\t- i\n",
                "\\ \n"] do
    roundTrip input

/-!
A metadata block prints from its own text, so indentation before it does not survive into the
indentation of its lines.
-/

/--
info: "\n %%%\nx := 1\n%%%": preserved
-/
#guard_msgs in
#eval show CommandElabM Unit from do
  roundTrip "\n %%%\nx := 1\n%%%"

/-!
A declaration whose Verso markup did not parse still pretty prints. The docstring keeps the text
that was written, which is what the parse-failure node contains.
-/

/-- Pretty prints the command that follows, or reports the error that stopped it. -/
elab "ppCmd " c:command : command => do
  try logInfo (toString (← liftCoreM <| PrettyPrinter.ppCommand ⟨c⟩))
  catch e => logInfo m!"FAILED: {e.toMessageData}"

/--
info: /-- A *document* ⏎
-/
def documented : Nat :=
  1
-/
#guard_msgs in
set_option doc.verso true in
ppCmd
/-- A *document* -/
def documented : Nat := 1

/--
info: /-- {unclosed -/
def undocumented : Nat :=
  1
-/
#guard_msgs in
set_option doc.verso true in
ppCmd
/-- {unclosed -/
def undocumented : Nat := 1
