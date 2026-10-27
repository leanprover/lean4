import Lean.Data.Markdown

/-!
This test ensures that it's possible to add ad-hoc extensions to the Markdown processor by
implementing tables and bare autolinks from GitHub's Markdown variant.
-/

open Lean Markdown

/-! # Tables -/

/-- A block of a document in which paragraphs may be tables. -/
inductive TableBlock (s : String.Slice) where
  /-- A Markdown block. -/
  | block (b : Block s)
  /-- A table: its header cells and its rows of cells, each cell parsed as inline content. -/
  | table (header : Array (Array (Inline s))) (rows : Array (Array (Array (Inline s))))

variable {s : String.Slice}

/-- The position after the leading spaces of `cell`. -/
def skipSpaces (cell : s.Subslice) : s.Pos := Id.run do
  let mut p := cell.startInclusive
  while h : p < cell.endExclusive do
    if p.get (String.Slice.Pos.ne_endPos_of_lt h) != ' ' then break
    p := p.next (String.Slice.Pos.ne_endPos_of_lt h)
  return p

/-- `cell` without its leading and trailing spaces. -/
def trimCell (cell : s.Subslice) : s.Subslice :=
  let trimmed := trimTrailing cell (· == ' ')
  subsliceClamped (skipSpaces trimmed) trimmed.endExclusive

/--
Splits a table row at its unescaped pipes (GFM §4.10). A pipe at the start or the end of the row
delimits nothing, and the spaces around each cell are dropped.
-/
def splitCells (row : s.Subslice) : Array s.Subslice := Id.run do
  let row := trimCell row
  let mut cells : Array s.Subslice := #[]
  let mut cellStart := row.startInclusive
  let mut p := row.startInclusive
  while h : p < row.endExclusive do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let c := p.get h'
    p := p.next h'
    if c == '\\' then
      if h2 : p < row.endExclusive then p := p.next (String.Slice.Pos.ne_endPos_of_lt h2)
    else if c == '|' then
      cells := cells.push (trimCell (subsliceClamped cellStart (p.prev?.getD p)))
      cellStart := p
  -- A trailing pipe leaves an empty final cell, and a leading pipe an empty first one.
  if cellStart < row.endExclusive then
    cells := cells.push (trimCell (subsliceClamped cellStart row.endExclusive))
  if cells.size > 0 && (cells[0]!.copy).isEmpty then cells := cells.extract 1 cells.size
  return cells

/-- Whether `cell` is a delimiter cell: optional colons around one or more hyphens. -/
def isDelimiterCell (cell : s.Subslice) : Bool :=
  let text := cell.copy
  let inner := (text.dropWhile (· == ':')).toString |>.dropEndWhile (· == ':') |>.toString
  !inner.isEmpty && inner.all (· == '-')

/--
Converts a raw block, recognizing a paragraph whose second line is a delimiter row as a table. The
cells are parsed as inline content with the document's reference definitions. Containers are not
descended into.
-/
def withTables (refs : RefTable s) (block : Block.Raw s) : TableBlock s :=
  match block with
  | .paragraph lines =>
    if h : 2 ≤ lines.size then
      -- A line from the block pass may still have its line ending.
      let rowOf (line : s.Subslice) := splitCells (trimTrailing line Char.isWhitespace)
      let header := rowOf lines[0]
      let delimiters := rowOf lines[1]
      if header.size == delimiters.size && delimiters.all isDelimiterCell then
        let parseCell (cell : s.Subslice) := parseInlines refs (.ofSubslice cell)
        let padded (cells : Array s.Subslice) : Array (Array (Inline s)) :=
          (Array.range header.size).map fun i =>
            match cells[i]? with
            | some cell => parseCell cell
            | none => #[]
        .table (header.map parseCell) ((lines.extract 2 lines.size).map (padded ∘ rowOf))
      else
        .block (parseInlinesInBlock refs block)
    else
      .block (parseInlinesInBlock refs block)
  | _ => .block (parseInlinesInBlock refs block)

/-- Parses `src` with tables, running the two passes with the table step between them. -/
def parseWithTables (src : String) : Array (TableBlock src.toSlice) :=
  let blocks := parseBlocks src.toSlice
  let refs := buildRefTable blocks
  blocks.map (withTables refs)

/-- Shows an inline by its constructor and source text. -/
partial def showInline : Inline s → String
  | .text r => r.copy
  | .code _ content _ => s!"`{content.text}`"
  | .italic _ cs _ => s!"*{showInlines cs}*"
  | .bold _ cs _ => s!"**{showInlines cs}**"
  | .link _ cs _ target => s!"[{showInlines cs}]({target.destination})"
  | .autolink _ url _ isEmail => s!"<{if isEmail then "mailto:" else ""}{url.copy}>"
  | .escape _ c => c.copy
  | .softBreak _ => "⏎"
  | i => s!"⟨{i.extent.copy}⟩"
where
  showInlines (cs : Array (Inline s)) : String := String.join (cs.toList.map showInline)

def showTableBlock : TableBlock s → String
  | .table header rows =>
    let showRow (cells : Array (Array (Inline s))) :=
      "[" ++ ", ".intercalate (cells.toList.map showInline.showInlines) ++ "]"
    s!"table{showRow header}{String.join (rows.toList.map showRow)}"
  | .block (.paragraph content) => s!"paragraph⟪{showInline.showInlines content}⟫"
  | .block _ => "block"

/-- info: ["table[a, b][c, *d*][e, ]"] -/
#guard_msgs in #eval (parseWithTables "| a | b |\n|---|:-:|\n| c | *d* |\ne\n").toList.map showTableBlock

-- Pipes are optional at the ends, escaped pipes are content, and reference links resolve.
/-- info: ["table[a|b, [c](/u)][1, 2]", "block"] -/
#guard_msgs in #eval
  (parseWithTables "a\\|b | [c]\n-- | --\n1 | 2\n\n[c]: /u\n").toList.map showTableBlock

-- A header whose cell count differs from the delimiter row's is a paragraph.
/-- info: ["paragraph⟪a | b⏎--- | --- | ---⟫"] -/
#guard_msgs in #eval (parseWithTables "a | b\n--- | --- | ---\n").toList.map showTableBlock

/-! # Bare autolinks -/

/-- Whether `lit` is the text at `p`, before `stop`. Returns the position after it. -/
def literalAt? (p stop : s.Pos) (lit : String) : Option s.Pos := Id.run do
  let mut p := p
  for c in lit.toSlice do
    if h : p < stop then
      let h' := String.Slice.Pos.ne_endPos_of_lt h
      if p.get h' != c then return none
      p := p.next h'
    else return none
  return some p

/-- Whether `c` may be part of a bare URL: anything but whitespace and `<`. -/
def isUrlChar (c : Char) : Bool := !c.isWhitespace && c != '<'

/--
The end of a bare URL that begins at `p`, after GFM's trailing punctuation rules: trailing `?`,
`!`, `.`, `,`, `:`, `*`, `_`, and `~` are excluded, and a trailing `)` only when it is unbalanced.
-/
def urlEnd (p stop : s.Pos) : s.Pos := Id.run do
  let mut q := p
  let mut parens : Int := 0
  while h : q < stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let c := q.get h'
    if !isUrlChar c then break
    if c == '(' then parens := parens + 1
    if c == ')' then parens := parens - 1
    q := q.next h'
  -- Trim trailing punctuation.
  repeat
    match q.prev? with
    | some r =>
      if p ≤ r then
        match r.get? with
        | some c =>
          if c == '?' || c == '!' || c == '.' || c == ',' || c == ':' || c == '*' || c == '_' ||
              c == '~' then
            q := r
          else if c == ')' && parens < 0 then
            q := r
            parens := parens + 1
          else break
        | none => break
      else break
    | none => break
  return q

/--
Splits the text inline `r` around the bare URLs in it: `http://`, `https://`, and `www.` at the
start of the text or after whitespace or `(`.
-/
def autolinksIn (r : s.Subslice) : Array (Inline s) := Id.run do
  let stop := r.endExclusive
  let mut out : Array (Inline s) := #[]
  let mut textStart := r.startInclusive
  let mut p := r.startInclusive
  let mut prev : Char := ' '
  while h : p < stop do
    let h' := String.Slice.Pos.ne_endPos_of_lt h
    let c := p.get h'
    let starts :=
      (prev.isWhitespace || prev == '(') &&
        ((literalAt? p stop "http://").isSome || (literalAt? p stop "https://").isSome ||
          (literalAt? p stop "www.").isSome)
    if starts then
      let q := urlEnd p stop
      if textStart < p then out := out.push (.text (subsliceClamped textStart p))
      let empty := subsliceClamped p p
      out := out.push (.autolink empty (subsliceClamped p q) empty false)
      textStart := q
      p := q
      prev := ' '
    else
      prev := c
      p := p.next h'
  if textStart < stop then out := out.push (.text (subsliceClamped textStart stop))
  return out

/-- Adds bare autolinks to inline content, leaving links, images, and code alone. -/
partial def withBareAutolinks (inlines : Array (Inline s)) : Array (Inline s) :=
  inlines.flatMap fun
    | .text r => autolinksIn r
    | .italic o cs c => #[.italic o (withBareAutolinks cs) c]
    | .bold o cs c => #[.bold o (withBareAutolinks cs) c]
    | i => #[i]

def showAutolinked (src : String) : List String :=
  (parseDocument src.toSlice).toList.filterMap fun
    | .paragraph content => some (showInline.showInlines (withBareAutolinks content))
    | _ => none

/-- info: ["see <https://x.y/a_(b)>, or (<www.x.y>) and *<http://x.y/>*."] -/
#guard_msgs in #eval showAutolinked "see https://x.y/a_(b), or (www.x.y) and *http://x.y/*."

-- Inside links and inline code, nothing changes; a URL inside a word is not a link.
/-- info: ["[https://x.y](/u) `https://x.y` ahttps://x.y"] -/
#guard_msgs in #eval showAutolinked "[https://x.y](/u) `https://x.y` ahttps://x.y"
