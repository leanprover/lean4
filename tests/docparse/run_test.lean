/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: David Thrane Christiansen
-/
import Lean.DocString.Parser
import Lean.DocString.View
import Lean.DocString.Formatter

/-!
This file tests the Verso parser.

Input files are expected to be snippets of code; their filename picks which parser is used.
-/

open Lean Doc Parser

/--
The greatest source position that any original leaf of `stx` reaches.
-/
partial def maxTailPos (stx : Syntax) : Option String.Pos.Raw :=
  match stx with
  | .node _ _ args =>
    args.foldl (init := none) fun acc a =>
      match acc, maxTailPos a with
      | none, x => x
      | x, none => x
      | some p, some q => some (if p < q then q else p)
  | .atom info _ => info.getTailPos?
  | .ident info .. => info.getTailPos?
  | .missing => none

def ppSyntax (stx : Syntax) : Std.Format := .nest 2 <| stx.formatStx (some 50) false

/--
Pushes an atom containing `str`, which the source does not contain.

The parsers that look ahead for a list marker pass what they found to a continuation. This renders
that value, so that the test output shows it.
-/
def fakeAtom (str : String) : ParserFn := fun _c s =>
  s.pushSyntax (.atom .none str)

open Std Format in
def ppStack (elts : Array Syntax) (number : Bool := false) : Format := Id.run do
  let mut stk : Format := .nil
  if h : elts.size = 0 then
    stk := " empty"
  else if elts.size = 1 then
    stk := "  " ++ ppSyntax elts[0]
  else
    for h : i in [0:elts.size] do
      let tm := ppSyntax (elts[i])
      let num := if number then .text s!"[{i}] " else .nil
      stk := stk ++ .group (" • " ++ num ++ nest 2 (.group tm)) ++ line
  pure stk

/-- A way in which a parsed tree fails to reproduce the input it was parsed from. -/
inductive SourceInfoError where
  /-- A leaf has source info that is not `.original`. -/
  | nonOriginalInfo (leaf : Syntax)
  /-- A leaf's text differs from the input at its recorded range. -/
  | textMismatch (leaf : Syntax) (expected : String) (actual : String)
  /-- A leaf's range overlaps the previous leaf or moves backwards. -/
  | overlap (leaf : Syntax) (pos : String.Pos.Raw)
  /-- The whitespace recorded on the leaves does not exactly fill the gap between two tokens. -/
  | gapNotCovered (pos : String.Pos.Raw) (leaf : Syntax)
  /-- A gap between tokens contains a non-whitespace character. -/
  | nonWhitespaceGap (pos : String.Pos.Raw) (char : Char)
  /-- Reprinting the syntax does not reproduce the input. -/
  | reprintMismatch (expected : String) (actual : Option String)
  /-- The syntax contains no tokens, so there is nowhere to record the input's whitespace. -/
  | noTokens
  /-- A leaf other than the first has leading whitespace. -/
  | lateLeading (leaf : Syntax)
  /-- A node has source info of its own, which only atoms and identifiers carry. -/
  | nodeInfo (kind : Name) (pos : Option String.Pos.Raw)

def SourceInfoError.describe : SourceInfoError → String
  | .nonOriginalInfo leaf => s!"leaf without original source info: {leaf}"
  | .textMismatch leaf expected actual =>
    s!"leaf text {toString (repr actual)} differs from input {toString (repr expected)} at {leaf.getPos?.map (·.byteIdx)}"
  | .overlap leaf pos =>
    s!"leaf {leaf} at {leaf.getPos?.map (·.byteIdx)} overlaps position {pos.byteIdx}"
  | .gapNotCovered pos leaf =>
    if leaf.isMissing then
      s!"input from position {pos.byteIdx} on is not covered by any token's source info"
    else
      s!"whitespace at {pos.byteIdx} not covered by the source info of {leaf}"
  | .nonWhitespaceGap pos c => s!"non-whitespace {toString (repr c)} at {pos.byteIdx} not part of any token"
  | .reprintMismatch expected actual =>
    s!"reprint produced {toString (repr actual)}\n  but the input was {toString (repr expected)}"
  | .noTokens => "no tokens to record the input's whitespace"
  | .lateLeading leaf =>
    s!"leaf {leaf} at {leaf.getPos?.map (·.byteIdx)} has leading whitespace, which only the first \
      leaf records"
  | .nodeInfo kind pos =>
    s!"node of kind {kind} at {pos.map (·.byteIdx)} has source info of its own, which only atoms \
      and identifiers carry"

/--
Checks the source info of `stx` against the part of `input` between `startPos` and `endPos`. The
check has six parts:

* No node has source info of its own; only atoms and identifiers carry any.
* Every leaf has `.original` source info whose text is exactly the input at its recorded range.
* The leaves are in order, and no two of them overlap.
* The leading and trailing whitespace recorded on the leaves exactly fills the gaps between
  tokens, and consists only of whitespace.
* Only the first leaf has leading whitespace, because every other leaf's is on the leaf before it.
* `Syntax.reprint` reproduces the input.

`choice` nodes are expected to be nonempty, with all of their children covering the same range.
Because Verso does not produce them, this test neither checks this invariant nor makes special
allowance for them.
-/
def validateSourceInfo (input : String) (startPos endPos : String.Pos.Raw) (stx : Syntax) :
    Except SourceInfoError Unit := do
  if let some (kind, pos) := nodeWithInfo stx then throw (.nodeInfo kind pos)
  let leaves := collectLeaves stx #[]
  -- A tree with no tokens has nowhere to record whitespace. This only arises for fragments and for
  -- documents with no content. In a whitespace-only docstring, the doc comment's own tokens record
  -- the whitespace instead.
  if leaves.isEmpty then
    if startPos == endPos then return () else throw .noTokens
  let mut pos := startPos
  let mut first := true
  for leaf in leaves do
    let .original leading start trailing stop := leaf.getHeadInfo
      | throw (.nonOriginalInfo leaf)
    if start < pos then throw (.overlap leaf pos)
    unless first || leading.isEmpty do
      throw (.lateLeading leaf)
    first := false
    unless leading.startPos == pos && leading.stopPos == start do
      throw (.gapNotCovered pos leaf)
    checkWhitespace input leading.startPos leading.stopPos
    let text := leafText leaf
    let expected := String.Pos.Raw.extract input start stop
    unless text == expected do
      throw (.textMismatch leaf expected text)
    unless trailing.startPos == stop do
      throw (.gapNotCovered stop leaf)
    checkWhitespace input trailing.startPos trailing.stopPos
    pos := trailing.stopPos
  unless pos == endPos do
    throw (.gapNotCovered pos .missing)
  let expected := String.Pos.Raw.extract input startPos endPos
  match stx.reprint with
  | some s => unless s == expected do throw (.reprintMismatch expected (some s))
  | none => throw (.reprintMismatch expected none)
where
  nodeWithInfo (stx : Syntax) : Option (Name × Option String.Pos.Raw) :=
    match stx with
    | .node info kind args =>
      match info with
      | .none => args.foldl (fun acc a => acc <|> nodeWithInfo a) none
      | _ => some (kind, info.getPos?)
    | _ => none
  collectLeaves (stx : Syntax) (leaves : Array Syntax) : Array Syntax :=
    match stx with
    | .node _ _ args => args.foldl (fun ls a => collectLeaves a ls) leaves
    | leaf => leaves.push leaf
  leafText : Syntax → String
    | .atom _ val => val
    | .ident _ rawVal _ _ => rawVal.toString
    | _ => ""
  checkWhitespace (input : String) (startPos stopPos : String.Pos.Raw) :
      Except SourceInfoError Unit := do
    let s := String.Pos.Raw.extract input startPos stopPos
    for c in s.toList do
      unless c.isWhitespace do
        throw (.nonWhitespaceGap startPos c)

/-!
Rendering of views.

These functions render a view as a `Repr` instance would, and leave out the syntax underlying each
view. The tree already shows that syntax. This section exists to pin the values that the
views and the content accessors decode.
-/

private def fmtAtom (stx : Syntax) : String := toString (repr stx.getAtomVal)

/-- Renders a delimiter as the characters it consists of. -/
private def fmtDelim (delim : VersoDelimiter) : String :=
  toString (repr delim.getVersoDelimiter)

private def fmtIdent (x : Ident) : String := toString x.getId.eraseMacroScopes
private def fmtDelims : Option (Syntax × Syntax) → String
  | none => "none"
  | some (o, c) => s!"some ({fmtAtom o}, {fmtAtom c})"

private def fmtArgVal (stx : TSyntax ``Parser.argVal) : String :=
  match ArgValView.of stx with
  | none => "<not an argument value>"
  | some (.str lit value) => s!"str (lit := {toString (repr lit.getString)}) (value := {toString (repr value)})"
  | some (.name x) => s!"name (x := {fmtIdent x})"
  | some (.num lit value) => s!"num (lit := {lit.getNat}) (value := {value})"

private def fmtArg (stx : TSyntax ``Parser.arg) : String :=
  match ArgView.of stx with
  | none => "<not an argument>"
  | some (.anon _ val) => s!"anon (val := {fmtArgVal val})"
  | some (.named _ parens name assign val) =>
    s!"named (parens := {fmtDelims parens}) (name := {fmtIdent name}) \
      (assign := {fmtAtom assign}) (val := {fmtArgVal val})"
  | some (.flag _ sign name isOn) =>
    s!"flag (sign := {fmtAtom sign}) (name := {fmtIdent name}) (isOn := {isOn})"

private def fmtArgs (args : TSyntaxArray ``Parser.arg) : String :=
  if args.isEmpty then "[]" else "[" ++ ", ".intercalate (args.toList.map fmtArg) ++ "]"

private def fmtTarget : LinkTargetView → String
  | .url _ o url c =>
    s!"url (opener := {fmtAtom o}) (url := {toString (repr url.getVersoLinkUrl)}) (closer := {fmtAtom c})"
  | .ref _ o name c =>
    s!"ref (opener := {fmtAtom o}) (name := {toString (repr name.getVersoRefName)}) (closer := {fmtAtom c})"

private def indentBy (n : Nat) : String := "".pushn ' ' n

/-- Renders a code element's delimiters and content. Math nests one of these, and so does `code`. -/
private def fmtCode (v : CodeView) : String :=
  s!"(opener := {fmtDelim v.opener}) (content := {toString (repr v.getVersoCode)}) \
    (closer := {fmtDelim v.closer})"

mutual
  private partial def fmtInline (n : Nat) (stx : TSyntax ``Parser.inline) :
      String :=
    let pad := indentBy n
    match InlineView.of stx with
    | none => s!"{pad}<not an inline>\n"
    | some (.text v) => s!"{pad}text (content := {toString (repr v.getVersoText)})\n"
    | some (.emph v) =>
      s!"{pad}emph (opener := {fmtDelim v.opener}) (closer := {fmtDelim v.closer})\n" ++
        fmtInlines (n + 2) v.content
    | some (.bold v) =>
      s!"{pad}bold (opener := {fmtDelim v.opener}) (closer := {fmtDelim v.closer})\n" ++
        fmtInlines (n + 2) v.content
    | some (.code v) => s!"{pad}code {fmtCode v}\n"
    | some (.math v) =>
      let mode := if v.mode matches .inline then "inline" else "display"
      s!"{pad}math (mode := {mode}) (marker := {fmtDelim v.marker}) {fmtCode v.code}\n"
    | some (.link v) =>
      s!"{pad}link (opener := {fmtAtom v.opener}) (closer := {fmtAtom v.closer}) \
        (target := {fmtTarget v.target})\n" ++
        fmtInlines (n + 2) v.content
    | some (.image v) =>
      s!"{pad}image (opener := {fmtAtom v.opener}) (alt := {toString (repr v.getAlt)}) \
        (closer := {fmtAtom v.closer}) (target := {fmtTarget v.target})\n"
    | some (.footnote v) =>
      s!"{pad}footnote (opener := {fmtAtom v.opener}) \
        (name := {toString (repr v.getName)}) (closer := {fmtAtom v.closer})\n"
    | some (.linebreak v) => s!"{pad}linebreak (newline := {fmtAtom v.newline})\n"
    | some (.role v) =>
      s!"{pad}role (braceOpen := {fmtAtom v.braceOpen}) (name := {fmtIdent v.name}) \
        (args := {fmtArgs v.args}) (braceClose := {fmtAtom v.braceClose}) \
        (brackets := {fmtDelims v.brackets})\n" ++
        fmtInlines (n + 2) v.content

  private partial def fmtInlines (n : Nat) (xs : TSyntaxArray ``Parser.inline) :
      String :=
    xs.foldl (init := "") fun acc i => acc ++ fmtInline n i

  private partial def fmtBlock (n : Nat) (stx : TSyntax ``Parser.block) :
      String :=
    let pad := indentBy n
    match BlockView.of stx with
    | none => s!"{pad}<not a block>\n"
    | some (.para v) => s!"{pad}para\n" ++ fmtInlines (n + 2) v.content
    | some (.ul v) => s!"{pad}ul\n" ++ fmtUnorderedItems (n + 2) v.items
    | some (.ol v) => s!"{pad}ol (start := {v.start})\n" ++ fmtOrderedItems (n + 2) v.items
    | some (.dl v) => s!"{pad}dl\n" ++ fmtDescItems (n + 2) v.items
    | some (.blockquote v) =>
      s!"{pad}blockquote (marker := {fmtAtom v.marker})\n" ++ fmtBlocks (n + 2) v.content
    | some (.codeblock v) =>
      let nm := match v.name? with | none => "none" | some x => s!"some {fmtIdent x}"
      s!"{pad}codeblock (openFence := {fmtDelim v.openFence}) (name? := {nm}) \
        (args := {fmtArgs v.args}) (content := {toString (repr v.getVersoCodeBlock)}) \
        (closeFence := {fmtDelim v.closeFence})\n"
    | some (.directive v) =>
      s!"{pad}directive (opener := {fmtDelim v.opener}) (name := {fmtIdent v.name}) \
        (args := {fmtArgs v.args}) (closer := {fmtDelim v.closer})\n" ++
        fmtBlocks (n + 2) v.content
    | some (.command v) =>
      s!"{pad}command (braceOpen := {fmtAtom v.braceOpen}) (name := {fmtIdent v.name}) \
        (args := {fmtArgs v.args}) (braceClose := {fmtAtom v.braceClose})\n"
    | some (.header v) =>
      s!"{pad}header (marker := {fmtDelim v.marker}) (level := {v.level})\n" ++
        fmtInlines (n + 2) v.content
    | some (.linkRef v) =>
      s!"{pad}linkRef (opener := {fmtAtom v.opener}) \
        (name := {toString (repr v.getName)}) (closer := {fmtAtom v.closer}) \
        (url := {toString (repr v.getUrl)})\n"
    | some (.footnoteRef v) =>
      s!"{pad}footnoteRef (opener := {fmtAtom v.opener}) \
        (name := {toString (repr v.getName)}) (closer := {fmtAtom v.closer})\n" ++
        fmtInlines (n + 2) v.content
    | some (.metadata v) =>
      s!"{pad}metadata (opener := {fmtAtom v.opener}) (fields := {v.fields.size}) \
        (closer := {fmtAtom v.closer})\n"

  private partial def fmtBlocks (n : Nat) (xs : TSyntaxArray ``Parser.block) :
      String :=
    xs.foldl (init := "") fun acc b => acc ++ fmtBlock n b

  private partial def fmtUnorderedItems (n : Nat) (items : Array UnorderedListItemView) : String :=
    items.foldl (init := "") fun acc i =>
      acc ++ s!"{indentBy n}item (marker := {fmtDelim i.marker})\n" ++ fmtBlocks (n + 2) i.contents

  private partial def fmtOrderedItems (n : Nat) (items : Array OrderedListItemView) : String :=
    items.foldl (init := "") fun acc i =>
      acc ++ s!"{indentBy n}item (marker := {fmtDelim i.marker})\n" ++ fmtBlocks (n + 2) i.contents

  private partial def fmtDescItems (n : Nat) (items : Array DescItemView) : String :=
    items.foldl (init := "") fun acc i =>
      acc ++ s!"{indentBy n}item (marker := {fmtAtom i.marker})\n" ++
        s!"{indentBy (n + 2)}term\n" ++ fmtInlines (n + 4) i.term ++
        s!"{indentBy (n + 2)}desc\n" ++ fmtBlocks (n + 4) i.desc
end

/--
Renders the views of everything on the parser's stack. Tries each entry as a block, then as an
inline, then as the smaller categories, so that one function serves every test config.
-/
private def fmtViews (stack : Array Syntax) : String := Id.run do
  let mut out := ""
  for stx in stack do
    let entries :=
      if stx.isOfKind ``Parser.document then
        (⟨stx⟩ : VersoDocument).getVersoBlocks.raw
      else if stx.isOfKind nullKind then stx.getArgs
      else #[stx]
    for e in entries do
      if (BlockView.of ⟨e⟩).isSome then out := out ++ fmtBlock 2 ⟨e⟩
      else if (InlineView.of ⟨e⟩).isSome then out := out ++ fmtInline 2 ⟨e⟩
      else if (ArgView.of ⟨e⟩).isSome then out := out ++ s!"  {fmtArg ⟨e⟩}\n"
      else if (ArgValView.of ⟨e⟩).isSome then out := out ++ s!"  {fmtArgVal ⟨e⟩}\n"
      else if let some t := LinkTargetView.of ⟨e⟩ then out := out ++ s!"  {fmtTarget t}\n"
      else if let some i := UnorderedListItemView.of ⟨e⟩ then
        out := out ++ s!"  item (marker := {fmtDelim i.marker})\n" ++ fmtBlocks 4 i.contents
      else if let some i := OrderedListItemView.of ⟨e⟩ then
        out := out ++ s!"  item (marker := {fmtDelim i.marker})\n" ++ fmtBlocks 4 i.contents
      else if let some i := DescItemView.of ⟨e⟩ then
        out := out ++ s!"  item (marker := {fmtAtom i.marker})\n" ++
          s!"    term\n" ++ fmtInlines 6 i.term ++ s!"    desc\n" ++ fmtBlocks 6 i.desc
      else if (`Lean.Doc.Parser).isPrefixOf e.getKind then
        -- A parser change that leaves an element with no view shows up here rather than as a
        -- line that quietly goes missing from the expectation. Syntax that is not a document element, such
        -- as the name in `nameAndArgs` or the result of a classifying parser, has no view.
        out := out ++ s!"  <no view for {e.getKind}>\n"
  return out

open Lean.Parser in
/--
Renders a parse error the way a compiler reports one: the error, the range it marks, and the line of
input with carets under that range. A closing note gives the length of the input prefix the parser
had consumed when it recorded the error, which is where the parse stopped rather than what the range
marks.

Tabs in the marked line become spaces, because a column counts a tab as one character and a caret
under a tab would otherwise land elsewhere. The `Input` line above shows the text as written.
-/
def fmtError (ictx : InputContext) (pos : String.Pos.Raw) (err : Error) : String := Id.run do
  let (start, stop?, err) := Doc.Parser.locateError ictx pos err
  let fileMap := ictx.fileMap
  let ⟨line, col⟩ := fileMap.toPosition start
  let stop? := stop?.map fileMap.toPosition
  -- The range is written as the compiler writes it in a diagnostic.
  let range :=
    match stop? with
    | some ⟨line', col'⟩ => s!"{line}:{col}-{line'}:{col'}"
    | none => s!"{line}:{col}"
  let lineStart := fileMap.lineStart line
  let next := fileMap.lineStart (line + 1)
  let lineStop := if lineStart < next then next else ictx.inputString.rawEndPos
  let text :=
    (String.Pos.Raw.extract ictx.inputString lineStart lineStop).chars.filter (· != '\n')
      |>.map (fun c => if c == '\t' then ' ' else c)
      |>.fold (init := "") String.push
  -- A range that runs past the marked line, and a range of no width, both get one caret.
  let width :=
    match stop? with
    | some ⟨line', col'⟩ => if line' == line then max 1 (col' - col) else max 1 (text.length - col)
    | none => 1
  let gutter := toString line
  let blank := "".pushn ' ' gutter.length
  let caret := "".pushn ' ' col |>.pushn '^' width
  return s!"{err}\n\
    {blank}--> {range}\n\
    {blank} |\n\
    {gutter} | {text}\n\
    {blank} | {caret}\n\
    {blank} = consumed input prefix: {pos} bytes\n"

def test (p : ParserFn) (rawInput : String) (validate : Bool) : IO String := do
  let ictx := mkInputContext rawInput "<input>"
  -- Parsing normalizes line endings, so `input` is the text the parser saw. The round-trip
  -- check compares the tree against that text.
  let input := ictx.inputString
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let s' := p.run ictx pmctx (getTokenTable env) (mkParserState input)
  let stk := ppStack <| s'.stxStack.extract 0 s'.stxStack.size

  let remaining : String :=
    if s'.pos ≥ input.rawEndPos then "All input consumed."
    else s!"Remaining:\n{repr (s'.pos.extract input input.rawEndPos)}"

  -- The harness validates the parser output exactly as produced. Every parser records the
  -- whitespace it passes in its tokens' source info. No token records the whitespace left at the
  -- end of a fragment, just as the closing delimiter records it at the end of a docstring, so the
  -- checked region ends where the parse did. The check also runs for parses that reported errors,
  -- so the expected output files pin how the harness treats recovered and partial output.
  let failed := !s'.allErrors.isEmpty
  let verdict :=
    if validate then
      let stop := s'.pos
      -- No token precedes the input, so its first token records the whitespace it starts with.
      -- The harness plays the role that the doc comment's opening delimiter plays in a file.
      let stack := setStartLeading 0 (mkNullNode (s'.stxStack.extract 0 s'.stxStack.size))
      match validateSourceInfo input 0 stop stack with
      | .ok () => "\nRound-trip OK"
      -- The Lean parser invokes the Verso parser only through a doc comment, whose `/--` token
      -- takes the whitespace after it as its trailing whitespace. A document with no tokens
      -- therefore always gets an empty region there, and arises only for fragments that this
      -- harness parses directly.
      | .error .noTokens => "\nRound-trip skipped: no tokens (the doc comment records the whitespace)"
      -- A parse that reported errors produces a partial tree, which is not expected to reprint.
      -- The verdict still records what the recovery left behind.
      | .error e =>
        if failed then s!"\nRound-trip not reproduced, as the parse reported errors: {e.describe}"
        else s!"\nRound-trip FAILED: {e.describe}"
    else
      "\nRound-trip not tested: this parser classifies input rather than producing document syntax"
  let given := s!"Input: {repr input}\n"
  -- Every outcome reports the stack the parser built and how much of the input it consumed.
  -- Syntax that reaches past the consumed input describes text the parse rewound out of.
  let overreach :=
    match maxTailPos (mkNullNode (s'.stxStack.extract 0 s'.stxStack.size)) with
    | some mp =>
      if mp > s'.pos then
        s!"\nSyntax covers unconsumed input: reaches {mp.byteIdx}, parse stopped at {s'.pos.byteIdx}"
      else ""
    | none => ""
  let result := s!"Final stack:\n{stk.pretty 50}\n{remaining}{overreach}{verdict}"
  if s'.allErrors.isEmpty then
    let views := fmtViews (s'.stxStack.extract 0 s'.stxStack.size)
    let views := if views.isEmpty then "" else s!"\nDecoded views:\n{views.dropEnd 1}"
    return s!"{given}Success! {result}{views}"
  else if let #[(p, _, err)] := s'.allErrors then
    return s!"{given}Failure: {fmtError ictx p err}{result}"
  else
    let mut errors := ""
    for (p, _, e) in s'.allErrors.qsort errLt do
      errors := (if errors.isEmpty then errors else errors ++ "\n") ++ s!"Failure: {fmtError ictx p e}"
    return s!"{given}{s'.allErrors.size} failures:\n{errors}\n{result}"
where
  errLt (x y : String.Pos.Raw × SyntaxStack × Error) : Bool :=
    let (p1, _, e1) := x
    let (p2, _, e2) := y
    p1 < p2 || p1 == p2 && toString e1 < toString e2

/--
Runs a block-level parser where a block starts. The token before a block records the whitespace
that precedes it, this line's indentation included. A fragment has no such token, so the harness
consumes that whitespace and `setStartLeading` records it on the fragment's first token.
-/
def blockStart (p : ParserFn) : ParserFn := ignoreFn lineTailWsFn >> p

/--
The test case's filename determines which parser tests it. The Boolean says whether
`validateSourceInfo` checks a successful parse against the input. It is `false` for parsers that
only classify input or discard their output.
-/
def testConfigs : List (String × ParserFn × Bool) := [
  ("metadataBlock", blockStart metadataBlockFn, true),
  ("metadataBlockNested", blockStart (metadataBlockFn {topLevel := false}), true),
  ("arg_val", valFn, true),
  ("arg", argFn, true),
  ("args", argsFn, true),
  ("nameAndArgs", nameAndArgsFn, true),
  ("inlineTextChar", inlineTextCharFn, false),
  ("manyInlineTextChar", (asTokenFn (many1Fn inlineTextCharFn)), true),
  ("text", textFn, true),
  ("emph", (emphFn {}), true),
  ("code", codeFn, true),
  ("codeIndented", codeFn {baseColumn := 2}, true),
  ("role", (roleFn {}), true),
  ("oneInline", (inlineFn {}), true),
  ("codeBlock", blockStart (codeBlockFn {}), true),
  ("header", blockStart (headerFn {}), true),
  ("blocks", blockStart (blocksFn {}), true),
  ("recoverBlock", blockStart (recoverBlock (blockFn {})), true),
  ("recoverBlocks", blockStart (recoverBlock (blocksFn {})), true),
  ("directive", blockStart (directiveFn {}), true),
  ("blockOpener", (ignoreFn blockOpenerFn), false),
  ("lookaheadUnorderedListMarker",
    blockStart (lookaheadUnorderedListMarker (fun type => fakeAtom s! "{toString (repr type)}")),
    false),
  ("lookaheadOrderedListMarker",
    blockStart <| lookaheadOrderedListMarker fun type i => fakeAtom s! "{toString (repr type)} {i}",
    false),
  ("block", blockStart (blockFn {}), true),
  ("document", documentFn, true),
  ("documentIndented", documentFn {baseColumn := 2}, true),
]

/--
Every syntax kind that the Verso parser can produce. The coverage test checks that each of these
kinds occurs in the output of at least one successfully parsed test file.
-/
def parserProducedKinds : List Name := [
  -- literal content and the delimiter runs
  Lean.Doc.versoTextKind,
  Lean.Doc.versoCodeKind,
  Lean.Doc.versoCodeLineKind,
  Lean.Doc.versoCodeBlockKind,
  ``Parser.headerMarker,
  ``Parser.listMarker,
  ``Parser.emphDelimiter,
  ``Parser.boldDelimiter,
  ``Parser.codeDelimiter,
  ``Parser.codeBlockFence,
  ``Parser.directiveDelimiter,
  -- argument values and arguments
  ``Parser.ArgVal.str,
  ``Parser.ArgVal.ident,
  ``Parser.ArgVal.num,
  ``Parser.Arg.anon,
  ``Parser.Arg.named,
  ``Parser.Arg.named_no_paren,
  ``Parser.Arg.flag_on,
  ``Parser.Arg.flag_off,
  -- link targets
  ``Parser.LinkTarget.url,
  ``Parser.LinkTarget.ref,
  -- inline elements
  ``Parser.Inline.text,
  ``Parser.Inline.emph,
  ``Parser.Inline.bold,
  ``Parser.Inline.code,
  ``Parser.Inline.inline_math,
  ``Parser.Inline.display_math,
  ``Parser.Inline.link,
  ``Parser.Inline.image,
  ``Parser.Inline.footnote,
  ``Parser.Inline.linebreak,
  ``Parser.Inline.role,
  -- list items
  ``Parser.ListItem.item,
  ``Parser.DescItem.item,
  -- block elements
  ``Parser.Block.para,
  ``Parser.Block.ul,
  ``Parser.Block.ol,
  ``Parser.Block.dl,
  ``Parser.Block.blockquote,
  ``Parser.Block.codeblock,
  ``Parser.Block.directive,
  ``Parser.Block.header,
  ``Parser.Block.link_ref,
  ``Parser.Block.footnote_ref,
  ``Parser.Block.metadata_block,
  ``Parser.Block.command,
]

partial def collectKinds (stx : Syntax) (kinds : Array Name) : Array Name :=
  match stx with
  | .node _ k args =>
    let kinds := if kinds.contains k then kinds else kinds.push k
    args.foldl (fun ks a => collectKinds a ks) kinds
  | _ => kinds

private def summarizeTarget : LinkTargetView → String
  | .url _ _ url _ => s!"url({toString (repr url.getVersoLinkUrl)})"
  | .ref _ _ name _ => s!"ref({toString (repr name.getVersoRefName)})"

private def isLinebreak (stx : TSyntax ``Parser.inline) : Bool :=
  match InlineView.of stx with
  | some (.linebreak ..) => true
  | _ => false

-- A structural summary of a document. It records every decoded value and no delimiter, because the
-- formatter renders canonically and may write a construct differently from how the source wrote
-- it.
mutual
  private partial def summarizeBlock (stx : TSyntax ``Parser.block) : String :=
    match BlockView.of stx with
    | none => s!"<{stx.raw.getKind}>"
    | some (.para v) => "para[" ++ summarizeBlockInlines v.content ++ "]"
    | some (.ul v) => "ul[" ++ " ".intercalate (v.items.toList.map summarizeUnorderedItem) ++ "]"
    | some (.ol v) =>
      s!"ol({v.start})[" ++ " ".intercalate (v.items.toList.map summarizeOrderedItem) ++ "]"
    | some (.dl v) => "dl[" ++ " ".intercalate (v.items.toList.map summarizeDesc) ++ "]"
    | some (.blockquote v) => "quote[" ++ summarizeBlocks v.content ++ "]"
    | some (.codeblock v) =>
      let name := v.name?.map (·.getId.eraseMacroScopes) |>.getD .anonymous
      s!"code({name}, {toString (repr v.getVersoCodeBlock)})"
    | some (.directive v) =>
      s!"directive({v.name.getId.eraseMacroScopes})[" ++ summarizeBlocks v.content ++ "]"
    | some (.command v) => s!"command({v.name.getId.eraseMacroScopes})"
    | some (.header v) =>
      s!"header({v.level})[" ++ summarizeBlockInlines v.content ++ "]"
    | some (.linkRef v) =>
      s!"linkRef({toString (repr v.getName)}, \
        {toString (repr v.getUrl)})"
    | some (.footnoteRef v) =>
      s!"footnoteRef({toString (repr v.getName)})[" ++
        summarizeBlockInlines v.content ++ "]"
    | some (.metadata v) => s!"metadata({v.fields.size})"

  private partial def summarizeBlocks (xs : TSyntaxArray ``Parser.block) :
      String :=
    " ".intercalate (xs.toList.map summarizeBlock)

  private partial def summarizeUnorderedItem (item : UnorderedListItemView) : String :=
    "[" ++ summarizeBlocks item.contents ++ "]"

  private partial def summarizeOrderedItem (item : OrderedListItemView) : String :=
    "[" ++ summarizeBlocks item.contents ++ "]"

  private partial def summarizeDesc (item : DescItemView) : String :=
    "[" ++ summarizeBlockInlines item.term ++ " | " ++ summarizeBlocks item.desc ++ "]"

  private partial def summarizeInlines (xs : TSyntaxArray ``Parser.inline) :
      String :=
    " ".intercalate (xs.toList.map summarizeInline)

  /--
  Summarizes the inline content that ends a block. The block break writes the newline that ends the
  last line, so the summary leaves a line break there out of the comparison.
  -/
  private partial def summarizeBlockInlines
      (xs : TSyntaxArray ``Parser.inline) : String :=
    summarizeInlines (if xs.back?.any isLinebreak then xs.pop else xs)

  private partial def summarizeInline (stx : TSyntax ``Parser.inline) :
      String :=
    match InlineView.of stx with
    | none => "<not an inline>"
    | some (.text v) => s!"text({toString (repr v.getVersoText)})"
    | some (.emph v) => "emph[" ++ summarizeInlines v.content ++ "]"
    | some (.bold v) => "bold[" ++ summarizeInlines v.content ++ "]"
    | some (.code v) => s!"code({toString (repr v.getVersoCode)})"
    | some (.math v) =>
      let mode := if v.mode matches .inline then "inline" else "display"
      s!"math({mode}, {toString (repr v.getVersoCode)})"
    | some (.link v) =>
      "link[" ++ summarizeInlines v.content ++ " | " ++ summarizeTarget v.target ++ "]"
    | some (.image v) =>
      s!"image({toString (repr v.getAlt)})[" ++ summarizeTarget v.target ++ "]"
    | some (.footnote v) => s!"footnote({toString (repr v.getName)})"
    | some (.linebreak ..) => "linebreak"
    | some (.role v) =>
      s!"role({v.name.getId.eraseMacroScopes})[" ++ summarizeInlines v.content ++ "]"
end

/-- Parses `input` as a document, or fails if it reports any error. -/
private def parseDocument (input : String) :
    IO (Option (TSyntaxArray ``Parser.block)) := do
  let ictx := mkInputContext input "<input>"
  let env : Environment ← mkEmptyEnvironment
  let s := documentFn.run ictx {env, options := {}} (getTokenTable env) (mkParserState input)
  let doc : VersoDocument := ⟨s.stxStack.back⟩
  if s.allErrors.isEmpty then return some doc.getVersoBlocks else return none

/--
Formats every test input in the current directory that parses as a document, and reports any whose
formatted form does not parse, or parses as a different document.
-/
def formatRoundTrip : IO UInt32 := do
  let files : Array String := (← System.FilePath.readDir ".").map (·.fileName)
    |>.filter (·.endsWith ".txt")
  let mut checked := 0
  let mut failed := #[]
  for file in files.qsort (· < ·) do
    let some blocks ← parseDocument (← IO.FS.readFile file) | continue
    if blocks.isEmpty then continue
    checked := checked + 1
    let before := blocks.map summarizeBlock
    let formatted := versoDocumentToString blocks
    match ← parseDocument formatted with
    | none => failed := failed.push s!"{file}: the formatted document does not parse\n  \
        formatted {toString (repr formatted)}"
    | some after =>
      let after := after.map summarizeBlock
      if before != after then
        failed := failed.push s!"{file}: the formatted document is a different document\n  \
          formatted {toString (repr formatted)}\n  before {before}\n  after  {after}"
  if failed.isEmpty then
    IO.println s!"All {checked} documents format to text that parses as the same document."
    return 0
  else
    IO.println s!"Of {checked} documents, {failed.size} do not survive formatting:"
    for f in failed do IO.println s!"  {f}"
    return 1

/-- The first node in `stx` with source info of its own, if any. -/
private partial def positionedNode? : Syntax → Option Syntax
  | stx@(.node info _ args) =>
    match info with
    | .none => args.findSome? positionedNode?
    | _ => some stx
  | _ => none

/--
Parses every test input in the current directory and reports any node in a parse result with source
info of its own. Atoms and identifiers carry the positions. A node's leaves are what locate it.
-/
def nodeInfo : IO UInt32 := do
  let files : Array String := (← System.FilePath.readDir ".").map (·.fileName)
    |>.filter (·.endsWith ".txt")
  let mut checked := 0
  let mut failed := #[]
  for file in files.qsort (· < ·) do
    let some blocks ← parseDocument (← IO.FS.readFile file) | continue
    checked := checked + 1
    for b in blocks do
      if let some n := positionedNode? b then
        failed := failed.push s!"{file}: node with its own source info: {n.getKind}"
  if failed.isEmpty then
    IO.println s!"No node in {checked} documents has source info of its own."
    return 0
  else
    IO.println s!"Of {checked} documents, {failed.size} contain nodes with their own source info:"
    for f in failed do IO.println s!"  {f}"
    return 1

/--
The first paragraph in `stx` whose content is nothing but whitespace, if any. The check reads the
decoded content through the views, so it states what a paragraph means.
-/
private partial def blankParagraph? (stx : Syntax) : Option Syntax :=
  match BlockView.of ⟨stx⟩ with
  | some (.para v) => if v.content.all (blankInline ·) then some stx else none
  | _ => stx.getArgs.findSome? blankParagraph?
where
  /--
  Whether an inline element contributes nothing but whitespace to its paragraph, judged by the text
  as it was written. An escape makes text content even where the character it escapes is a space, so
  `\ ` on a line of its own is a paragraph whose decoded content is a single space.
  -/
  blankInline (inl : TSyntax ``Parser.inline) : Bool :=
    match InlineView.of inl with
    | some (.linebreak ..) => true
    | some (.text v) => v.getVersoTextSource.all Char.isWhitespace
    | _ => false

/--
Parses every test input in the current directory and reports any paragraph written as nothing but
whitespace. A paragraph contains content, so a run of empty lines is not a paragraph.
-/
def blankParagraphs : IO UInt32 := do
  let files : Array String := (← System.FilePath.readDir ".").map (·.fileName)
    |>.filter (·.endsWith ".txt")
  let mut checked := 0
  let mut failed := #[]
  for file in files.qsort (· < ·) do
    let some blocks ← parseDocument (← IO.FS.readFile file) | continue
    checked := checked + 1
    for b in blocks do
      if let some p := blankParagraph? b then
        failed := failed.push s!"{file}: paragraph with no content: {p}"
  if failed.isEmpty then
    IO.println s!"No paragraph in {checked} documents is empty."
    return 0
  else
    IO.println s!"Of {checked} documents, {failed.size} contain an empty paragraph:"
    for f in failed do IO.println s!"  {f}"
    return 1

/--
Parses every test input in the current directory and reports any kind from
`parserProducedKinds` that occurs in no successful parse result.
-/
def coverage : IO UInt32 := do
  let mut seen : Array Name := #[]
  let files : Array String := (← System.FilePath.readDir ".").map (·.fileName)
    |>.filter (·.endsWith ".txt")
  let env : Environment ← mkEmptyEnvironment
  let pmctx : ParserModuleContext := {env := env, options := {}}
  let tokens := getTokenTable env
  for file in files do
    let kind := file.takeWhile (· != '_')
    let some (p, _) := testConfigs.lookup kind.copy
      | continue
    let input ← IO.FS.readFile file
    let ictx := mkInputContext input "<input>"
    let s' := p.run ictx pmctx tokens (mkParserState input)
    if s'.allErrors.isEmpty then
      for stx in s'.stxStack.extract 0 s'.stxStack.size do
        seen := collectKinds stx seen
  let missing := parserProducedKinds.filter (!seen.contains ·)
  if missing.isEmpty then
    IO.println "All parser-produced syntax kinds are covered."
    return 0
  else
    IO.println "Syntax kinds not covered by any successfully parsed test file:"
    for k in missing do
      IO.println s!"  {k}"
    return 1

def main : List String → IO UInt32
  | [inputFile] => do
    let inputFile : System.FilePath := inputFile
    if inputFile.isAbsolute then
      IO.eprintln s!"Expected a relative path, got {inputFile}"
      return 2
    unless (← inputFile.pathExists) do
      IO.eprintln s!"File not found: {inputFile}"
      return 3
    let [file] := inputFile.components
      | IO.eprintln "Expected file in current directory"
        return 4
    let kind := file.takeWhile (· != '_')
    if kind == "coverage" then
      return (← coverage)
    if kind == "format" then
      return (← formatRoundTrip)
    if kind == "nodeinfo" then
      return (← nodeInfo)
    if kind == "blankPara" then
      return (← blankParagraphs)
    let some (p, validate) := testConfigs.lookup kind.copy
      | IO.eprintln s!"Not found in test configs: {kind}"
        return 5
    IO.println <| ← test p (← IO.FS.readFile inputFile) validate
    return 0
  | args => do
    IO.eprintln s!"Expected precisely one argument, got {args}"
    return 1
