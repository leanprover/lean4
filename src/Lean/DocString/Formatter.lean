/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module
prelude
public import Lean.PrettyPrinter.Formatter
public import Lean.DocString.Syntax
import Init.Data.Range.Polymorphic.Iterators
meta import Init.Data.Range.Polymorphic.GetElemTactic
import Lean.DocString.Parser
import Lean.DocString.View


namespace Lean.Doc.Parser

open Lean.PrettyPrinter Formatter
open Lean.Syntax.MonadTraverser

open Lean.Doc

def atomString : Syntax → String
  | .node _ _ #[x] => atomString x
  | .atom _ x => x
  | stx => s!"NON-ATOM {stx}"

def identString : Syntax → String
  | .node _ _ #[x] => identString x
  | .ident _ _ x _ => toString x.eraseMacroScopes
  | stx => s!"NON-IDENT {stx}"

/--
The zero-width space between two delimiters that the parser would otherwise read as one longer
delimiter. Verso has no other way to put such elements next to each other.
-/
def zwsp : String := "\u200B"

/-- The kind of list that a block is. -/
inductive ListKind where
  /-- A list whose items are numbered. -/
  | ordered
  /-- A list whose items are bulleted. -/
  | unordered
deriving BEq

/-- The kind of list a block is, when it is one. -/
def listKind? (stx : Syntax) : Option ListKind :=
  match BlockView.of ⟨stx⟩ with
  | some (.ul ..) => some .unordered
  | some (.ol ..) => some .ordered
  | _ => none

/--
A choice of list marker. An unordered list uses `*` or `-`. An ordered list uses a number followed
by `.` or `)`. `alternate` selects the second option of each pair.
-/
structure MarkerChoice where
  /-- The kind of list the marker introduces. -/
  kind : ListKind
  /--
  Whether the marker is `-`, or a number followed by `)`, instead of the default style which uses
  `*` and `.` respectively.
  -/
  alternate : Bool

/--
Chooses a list marker for `stx`, given the choice for the list directly before it. The result is
`none` when `stx` is not a list.

Subsequent lists may not use the same marker style. Otherwise, the parser will consider them to be
the same list.
-/
def markerFor (prev? : Option MarkerChoice) (stx : Syntax) :
    Option MarkerChoice :=
  match listKind? stx with
  | none => none
  | some kind =>
    let alternate :=
      match prev? with
      | some previous => kind == previous.kind && !previous.alternate
      | none => false
    some { kind, alternate }

/-- The monad for printing Verso syntax: the current indentation and the output so far. -/
abbrev VersoStringM := ReaderT Nat (StateM String)

/-- Appends `s` to the output. -/
def out (s : String) : VersoStringM Unit := modify (· ++ s)

/-- Indents a block that begins on a fresh line. -/
def startBlock : VersoStringM Unit := do
  let s ← get
  if s.endsWith "\n" then
    let i ← read
    out ("".pushn ' ' i)

/--
Whether the newline that ends `s` is one that an escape wrote, which makes it content rather than a
line ending. Each pair of backslashes denotes one literal backslash, so the newline is escaped when
an odd number of them precedes it.
-/
def endsWithEscapedNewline (s : String.Slice) : Bool :=
  s.endsWith "\n" &&
    ((s.dropEnd 1).takeEndWhile (· == '\\') |>.chars.fold (init := false) fun odd _ => !odd)

/--
The number of line endings at the end of `s`, counted up to two. A newline that an escape wrote is
content, so it ends the count.
-/
def trailingLineEndings (s : String.Slice) : Nat :=
  if !s.endsWith "\n" || endsWithEscapedNewline s then 0
  else
    let s := s.dropEnd 1
    if !s.endsWith "\n" || endsWithEscapedNewline s then 1 else 2

/-- Ends a block with a blank line, and never with more than one. -/
def endBlock : VersoStringM Unit := do
  let s ← get
  out ("".pushn '\n' (2 - trailingLineEndings s.toSlice))

/--
Prints `value` as text.
-/
def textString (atLineStart : Bool) (value : String) : String :=
  let text := escaped value
  if atLineStart && needsEscape value then "\\" ++ text else text
where
  /-- Puts the escape character before each character that ends a text run. -/
  escaped (value : String) : String :=
    value.foldl (init := "") fun out c =>
      if isSpecial c then out.push '\\' |>.push c else out.push c
  /-- Whether `c` is a special character in Verso that requires escaping in text. -/
  isSpecial : Char → Bool
    -- A newline in text content comes from an escaped newline in the source. Printed without its
    -- escape, it would become a line break or a block boundary instead of content.
    | '\\' | '*' | '_' | '[' | ']' | '{' | '}' | '`' | '!' | '$' | '\n' => true
    | _ => false
  /--
  Whether the parser would read the start of `text` as something other than text when `text` starts
  a line, so that its first character needs an escape. The whitespace that begins a line is skipped,
  and a block opens after it. A list marker opens a list when a space or a line break follows it,
  and the end of the text counts as a line break. A header's `#` run and a blockquote's `>` open a
  block with nothing after them.
  -/
  needsEscape (text : String) : Bool :=
    let afterDigits := text.dropWhile (·.isDigit)
    -- Escaping the space that begins a line also puts anything after it past the position where a
    -- block may open.
    text.startsWith " " || text.startsWith "\t" ||
    text.startsWith "#" || text.startsWith ">" ||
    text == "-" || text.startsWith "- " ||
    text == "+" || text.startsWith "+ " ||
    text.startsWith ": " || text.startsWith ":::" ||
    text.startsWith "%%%" ||
    (text.front?.any (·.isDigit) &&
      (afterDigits.startsWith "." || afterDigits.startsWith ")") &&
      (afterDigits.drop 1).front?.all (· == ' '))

/-- Whether `s` consists entirely of whitespace. -/
def blank (s : String.Slice) : Bool := s.all (fun c : Char => c.isWhitespace)

/-- The number of leading spaces in `s`. -/
def indentation (s : String.Slice) : Nat := Id.run do
  let mut n : Nat := 0
  for c in s do
    if c != ' ' then break
    n := n + 1
  n

/--
Prints source text with an indentation of `i` spaces in place of the indentation it was written
with. Blank lines are empty and unindented.
-/
def reindented (i : Nat) (src : String) : String := Id.run do
  let common :=
    (src.lines.filter (!blank ·) |>.map indentation
      |>.fold (init := none) fun least n => (least.map (min n)).getD n).getD 0
  let mut out := ""
  -- A blank line is written only once a line with content follows it, so the blank lines before
  -- the first and after the last never reach the output.
  let mut pending := 0
  for l in src.lines do
    if blank l then
      unless out.isEmpty do pending := pending + 1
    else
      unless out.isEmpty do out := out.pushn '\n' (pending + 1)
      pending := 0
      out := out ++ "".pushn ' ' i ++ l.drop common
  return out

/--
Prints `value` as inline code, with delimiters that are longer than any run of backticks in the
content. Padding spaces are added if needed, and empty code is mapped to a single space.
-/
def codeString (value : String) : String :=
  let padded :=
    if value.isEmpty then " "
    else if value.startsWith "`" || value.endsWith "`" || versoCodeBoundarySpaces value then
      " " ++ value ++ " "
    else value
  let delim := "".pushn '`' (longestBacktickRun padded + 1)
  delim ++ padded ++ delim

/--
The number of delimiter characters to print around an emphasis or bold element whose content is
`inls`. A run is one character longer than the longest run of the same character printed inside it.
The parser reads a nested run as nested only when it is shorter than the run around it.
-/
partial def emphRun (char : Char) (inls : TSyntaxArray ``Parser.inline) : Nat :=
  1 + depth inls
where
  /-- The greatest number of `char`-delimited elements nested inside one another in `inls`. -/
  depth (inls : TSyntaxArray ``Parser.inline) : Nat :=
    inls.foldl (init := 0) fun best inl =>
      match InlineView.of inl with
      | some (.emph v) =>
        max best ((if char == '_' then 1 else 0) + depth v.content)
      | some (.bold v) =>
        max best ((if char == '*' then 1 else 0) + depth v.content)
      | some (.link v) => max best (depth v.content)
      | some (.role v) => max best (depth v.content)
      | _ => best

/--
The number of colons in a directive's delimiters. A directive uses three colons, or one more than
the delimiters of the deepest directive nested inside it, whichever is greater.
-/
partial def directiveRun (blks : TSyntaxArray ``Parser.block) : Nat :=
  max 3 (deepest blks)
where
  /-- The number of colons needed to enclose every directive in `blks`. -/
  deepest (blks : TSyntaxArray ``Parser.block) : Nat :=
    blks.foldl (init := 0) fun best blk =>
      match BlockView.of blk with
      | some (.directive v) => max best (max 3 (deepest v.content) + 1)
      | some (.blockquote v) => max best (deepest v.content)
      | some (.ul v) =>
        v.items.foldl (init := best) fun best item => max best (deepest item.contents)
      | some (.ol v) =>
        v.items.foldl (init := best) fun best item => max best (deepest item.contents)
      | some (.dl v) =>
        v.items.foldl (init := best) fun best item => max best (deepest item.desc)
      | _ => best

/--
Whether an inline element prints as nothing but whitespace.
-/
def printsBlank (inl : TSyntax ``Parser.inline) : Bool :=
  if let some _ := LinebreakView.of inl then true
  -- Text prints with an escape wherever it contains a character that would otherwise end a run, and
  -- a printed escape is not whitespace. The first element of a paragraph prints at the start of a
  -- line, where an escape also guards a character that would open a block.
  else if let some txt := TextView.of inl then
    textString (atLineStart := true) txt.getVersoText |>.all Char.isWhitespace
  else false

/--
Whether a block's parser reads it only at the start of a line, so that it cannot follow a list
item's marker on the marker's own line.
-/
def needsLineStart (stx : TSyntax ``Parser.block) : Bool :=
  match BlockView.of stx with
  | some (.header ..) | some (.linkRef ..) | some (.footnoteRef ..) | some (.metadata ..) => true
  | _ => false

/--
Whether an inline element is written as nothing but whitespace.
-/
def blankInline (inl : TSyntax ``Parser.inline) : Bool :=
  if let some _ := LinebreakView.of inl then true
  else if let some txt := TextView.of inl then txt.getVersoTextSource.all Char.isWhitespace
  else false

/--
Whether `stx` is a paragraph that would print as nothing but whitespace. The formatter leaves such
a paragraph out. The parser produces only paragraphs that contain content.
-/
def blankParagraph (stx : Syntax) : Bool :=
  if let some para := ParaView.of ⟨stx⟩ then para.content.all (blankInline ·)
  else false

/-- Whether `stx` is a hard line break. -/
def isLinebreak (stx : Syntax) : Bool :=
  if let some _ := LinebreakView.of ⟨stx⟩ then true else false

/--
If `inls` contains a single self-delimiting inline, then it is returned. Otherwise,
the result is `none`.

This determines whether the body of a role needs to be wrapped in `[` and `]`.
-/
def selfDelimiting? (inls : TSyntaxArray ``Parser.inline) :
    Option (TSyntax ``Parser.inline) :=
  if h : inls.size = 1 then
    let inl := inls[0]
    match InlineView.of inl with
    | some (.emph ..) | some (.bold ..)
    | some (.code ..) | some (.math ..)
    | some (.image ..) | some (.role ..) => some inl
    | some (.text ..) | some (.linebreak ..)
    | some (.link ..) | some (.footnote ..)
    | none => none
  else none

/--
The last character printed for an inline element, when it is a delimiter.

Adjacency checks use this. The backticks of two adjacent code elements must be kept apart.
-/
partial def closerChar (inl : TSyntax ``Parser.inline) : Option Char :=
  match InlineView.of inl with
  | some (.emph ..) => some '_'
  | some (.bold ..) => some '*'
  | some (.code ..) => some '`'
  | some (.math ..) => some '`'
  | some (.link v) => targetCloser v.target
  | some (.image v) => targetCloser v.target
  | some (.footnote ..) => some ']'
  | some (.role v) =>
    -- The formatter decides whether to print the role's own brackets, whatever the source wrote.
    if let some inl := selfDelimiting? v.content then closerChar inl else some ']'
  | _ => none
where
  /-- The bracket that closes a link's or an image's target. -/
  targetCloser : LinkTargetView → Option Char
    | .url .. => some ')'
    | .ref .. => some ']'

/-- The first character printed for an inline element, when it is a delimiter or marker. -/
def openerChar (stx : Syntax) : Option Char :=
  match InlineView.of ⟨stx⟩ with
  | some (.emph ..) => some '_'
  | some (.bold ..) => some '*'
  | some (.code ..) => some '`'
  | some (.math ..) => some '$'
  | _ => none

/--
Whether printing `inl` without the role's brackets would run its closing delimiter into the opening
delimiter of `next?`.
-/
def runsInto (inl : TSyntax ``Parser.inline)
    (next? : Option Syntax) : Bool :=
  match closerChar inl, next?.bind openerChar with
  | some a, some b => a == b
  | _, _ => false

/--
Whether the closing backtick of `inl` would merge with the opening backtick of `next?` into one
longer delimiter.
-/
def mergesInto (inl : TSyntax ``Parser.inline) (next? : Option Syntax) : Bool :=
  match closerChar inl, next?.bind openerChar with
  | some '`', some '`' => true
  | _, _ => false

/-- Whether the text printed for `inls` begins with a space. -/
def leadingSpace (inls : TSyntaxArray ``Parser.inline) : Bool :=
  if let some txt := inls[0]?.bind TextView.of then txt.getVersoText.startsWith " "
  else false

/-- Prints a link target. -/
def linkTargetToString : LinkTargetView → VersoStringM Unit
  | .ref _ _ content _ => do
    out "["
    out content.getVersoRefName
    out "]"
  | .url _ _ content _ => do
    out "("
    out (escapeVersoLinkUrl content.getVersoLinkUrl)
    out ")"

partial def versoSyntaxToString'
    (stx : Syntax) (next? : Option Syntax := none) (atLineStart := false) (alternate := false) :
    VersoStringM Unit := do
  if stx.getKind == nullKind then
    seq stx.getArgs
  else if let some v := ArgValView.of ⟨stx⟩ then
    match v with
    | .str s _ => out <| atomString s.raw
    | .num n _ => out <| atomString n.raw
    | .name x => out <| identString x.raw
  else if let some v := ArgView.of ⟨stx⟩ then
    match v with
    | .anon _ val => versoSyntaxToString' val.raw
    | .named _ _ x _ val =>
      out "("
      out <| identString x.raw
      out " := "
      versoSyntaxToString' val.raw
      out ")"
    | .flag _ _ x isOn =>
      out <| if isOn then "+" else "-"
      out <| identString x.raw
  else if let some v := LinkTargetView.of ⟨stx⟩ then
    linkTargetToString v
  else if let some v := InlineView.of ⟨stx⟩ then
    match v with
    | .text v => out <| textString atLineStart v.getVersoText
    | .emph v => emphLike '_' v.content
    | .bold v => emphLike '*' v.content
    | .link v =>
      out "["
      seq (v.content.map (·.raw))
      out "]"
      linkTargetToString v.target
    | .image v =>
      out "!["
      out (escapeVersoImageAlt v.getAlt)
      out "]"
      linkTargetToString v.target
    | .role v =>
      out "{"
      out <| identString v.name.raw
      for arg in v.args do
        out " "
        versoSyntaxToString' arg.raw
      out "}"
      -- A role whose content is a single self-delimiting element needs no brackets. The formatter
      -- prints that shorter form, whatever the source wrote.
      let needsBrackets :=
        if let some inl := selfDelimiting? v.content then runsInto inl next? else true
      if needsBrackets then
        out "["
        seq (v.content.map (·.raw))
        out "]"
      else
        seq (v.content.map (·.raw))
    | .code v =>
      out <| codeString v.getVersoCode
    | .footnote v =>
      out "[^"
      out v.getName
      out "]"
    | .linebreak .. =>
      out "\n"
    | .math v =>
      out <| match v.mode with | .inline => "$" | .display => "$$"
      out <| codeString v.getVersoCode
  else if let some v := BlockView.of ⟨stx⟩ then
    match v with
    | .header v =>
      startBlock
      out <| "#".pushn '#' v.level ++ " "
      seq (v.content.map (·.raw))
      endBlock
    | .para v =>
      unless v.content.all (blankInline ·) do
        startBlock
        -- A paragraph whose content prints as nothing but whitespace would parse back as no
        -- paragraph, so it takes an escape to keep the line. Content that prints an escape of its
        -- own already keeps it.
        if v.content.all (printsBlank ·) then out "\\"
        seq (v.content.map (·.raw)) (lineStart := true)
        endBlock
    | .ul v =>
      let marker := if alternate then "- " else "* "
      for item in v.items do
        startBlock
        itemStart marker item.contents
        withReader (· + marker.length) (seq (item.contents.map (·.raw)))
        endBlock
      endBlock
    | .ol v =>
      let mut n := v.start
      for item in v.items do
        startBlock
        let marker := if alternate then s!"{n}) " else s!"{n}. "
        itemStart marker item.contents
        withReader (· + marker.length) (seq (item.contents.map (·.raw)))
        endBlock
        n := n + 1
      endBlock
    | .blockquote v =>
      startBlock
      out <| if v.content.isEmpty then ">" else "> "
      withReader (· + 2) (seq (v.content.map (·.raw)))
      endBlock
    | .codeblock v =>
      startBlock
      let fence := "".pushn '`' (max 3 (longestBacktickRun v.getVersoCodeBlock + 1))
      out fence
      if let some name := v.name? then
        out <| identString name.raw
        for arg in v.args do
          out " "
          versoSyntaxToString' arg.raw
      out "\n"
      let i ← read
      -- The closing fence stands at the start of a line. The contents therefore print as whole
      -- lines, and the last element of the split is the fence's own indentation.
      let written := v.getVersoCodeBlock
      let contents := if written.isEmpty || written.endsWith "\n" then written else written ++ "\n"
      out <| contents
        |>.split '\n'
        |>.map (fun (l : String.Slice) => "".pushn ' ' i ++ l)
        |>.toList
        |> "\n".intercalate
      out fence
      endBlock
    | .directive v =>
      startBlock
      let delim := "".pushn ':' (directiveRun v.content)
      out delim
      out <| identString v.name.raw
      for arg in v.args do
        out " "
        versoSyntaxToString' arg.raw
      out "\n"
      seq (v.content.map (·.raw))
      let i ← read
      out <| "".pushn ' ' i
      out delim
      endBlock
    | .command v =>
      startBlock
      out <| "{"
      out <| identString v.name.raw
      for arg in v.args do
        out " "
        versoSyntaxToString' arg.raw
      out "}"
      endBlock
    | .dl v =>
      for item in v.items do
        startBlock
        out ":"
        -- The space after the colon is part of the term. The formatter writes a space only for a
        -- term that does not begin with one.
        unless leadingSpace item.term do out " "
        seq (item.term.map (·.raw))
        endBlock
        withReader (· + 2) (seq (item.desc.map (·.raw)))
        endBlock
      endBlock
    | .linkRef v =>
      startBlock
      out "["
      out v.getName
      out "]:"
      out " "
      out v.getUrl
      endBlock
    | .footnoteRef v =>
      startBlock
      out "[^"
      out v.getName
      out "]:"
      out " "
      seq (v.content.map (·.raw))
      endBlock
    | .metadata v =>
      -- The contents are Lean terms. The formatter prints them as they were written, between
      -- delimiters that are each on their own line.
      startBlock
      let i ← read
      match stx.getSubstring? (withLeading := false) (withTrailing := false) with
      | some source =>
        -- The block as it was written, reindented to match the delimiter.
        out (reindented i source.toString)
      | none =>
        -- A block that a metaprogram built has no text, so the delimiters are printed and the
        -- contents come from the syntax.
        let contents := reindented i (v.contents.raw.reprint.getD "")
        out "%%%\n"
        unless contents.isEmpty do
          out contents
          out "\n"
        out ("".pushn ' ' i ++ "%%%")
      endBlock
  else
    out (toString stx)
where
  /--
  Prints a list item's marker. The item's contents follow on the marker's line, except where the
  first block is one that the parser reads only at the start of a line.
  -/
  itemStart (marker : String) (contents : TSyntaxArray ``Parser.block) : VersoStringM Unit := do
    let alone := marker.dropEndWhile (· == ' ') |>.copy
    match contents[0]? with
    | none => out alone
    | some first => if needsLineStart first then out (alone ++ "\n") else out marker

  /-- Prints sibling elements in order, tracking line starts and list runs. -/
  seq (stxs : Array Syntax) (lineStart := false) : VersoStringM Unit := do
    -- A blank paragraph prints nothing, so `seq` drops it before rendering its neighbors. A blank
    -- paragraph might otherwise lead to incorrectly failing to pick an alternate marker for a list
    -- item.
    let stxs := stxs.filter (!blankParagraph ·)
    let mut atLineStart := lineStart
    let mut prev? : Option MarkerChoice := none
    for h : i in 0...stxs.size do
      let stx := stxs[i]
      let choice? := markerFor prev? stx
      versoSyntaxToString' stx stxs[i+1]? atLineStart (choice?.any (·.alternate))
      if let some next := stxs[i+1]? then
        -- A role prints its brackets where its content would run into the next element. Only the
        -- other elements need the separator.
        let isRole := if let some _ := RoleView.of ⟨stx⟩ then true else false
        if !isRole && mergesInto ⟨stx⟩ next then out zwsp
      atLineStart := isLinebreak stx
      prev? := choice?

  /--
  Prints an emphasis or bold element.
  -/
  emphLike (char : Char)
      (inls : TSyntaxArray ``Parser.inline) : VersoStringM Unit := do
    let delim := "".pushn char (emphRun char inls)
    out delim
    if inls[0]?.bind (openerChar ·.raw) == some char then out zwsp
    seq (inls.map (·.raw))
    out delim

/--
Leaves `s` with a single newline at its end, where it has one. Each block prints with a blank line
after it, which separates it from the next block. The last block in a document has no next block.
-/
def oneTrailingNewline (s : String) : String :=
  if s.endsWith "\n" then s.dropEndWhile '\n' |>.copy |>.push '\n' else s

/--
Renders `stx` as Verso, ending with the blank line that separates a block from the block after it.
-/
def separatedToString (stx : Syntax) (alternate := false) : String :=
  versoSyntaxToString' stx (alternate := alternate) |>.run 0 |>.run "" |>.2

public def versoSyntaxToString (stx : Syntax) (alternate := false) : String :=
  oneTrailingNewline (separatedToString stx alternate)

/--
Renders each of `blocks` as Verso. A list's marker depends on the blocks before it, so this
renders the blocks in order.
-/
def versoBlocksToString (blocks : TSyntaxArray ``Parser.block) :
    Vector String blocks.size :=
  blocks.toVector.mapM (m := StateM (Option MarkerChoice)) (fun b => do
      -- A blank paragraph prints nothing and leaves the list run unchanged. It therefore cannot
      -- separate two lists of the same kind that the markers have to keep apart.
      if blankParagraph b.raw then return ""
      let choice? := markerFor (← get) b.raw
      set choice?
      pure (separatedToString b.raw (choice?.any (·.alternate))))
    |>.run' none

/-- Renders a sequence of blocks as Verso. -/
public def versoDocumentToString (blocks : TSyntaxArray ``Parser.block) :
    String :=
  oneTrailingNewline ((versoBlocksToString blocks).foldl (· ++ ·) "")

@[builtin_formatter Lean.Doc.Parser.document]
public def document.formatter : Formatter := concat do
  let blocks : TSyntaxArray ``Parser.block := (⟨← getCur⟩ : VersoDocument)
  -- A marker depends on the blocks before its list, so `versoBlocksToString` renders every
  -- block before the loop below pushes any.
  let rendered := versoBlocksToString blocks
  visitArgs <| visitArgs do
    for h : k in 0...blocks.size do
      -- `visitArgs` walks the arguments from the right, so the first block pushed is the
      -- document's last. That block needs no separator after it.
      let text := rendered[blocks.size - 1 - k]
      push (if k == 0 then oneTrailingNewline text else text)
      goLeft
