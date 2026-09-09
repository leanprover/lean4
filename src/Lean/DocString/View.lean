/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/

module

prelude
public import Lean.DocString.Types
public import Lean.Parser.Term.Basic
public import Lean.DocString.Syntax
meta import Lean.DocString.Syntax

set_option linter.missingDocs true

namespace Lean.Doc


public section

/-!
This module defines views of the concrete syntax of Verso documents.

The syntax declarations in `Lean.DocString.Syntax` specify the shapes of the trees that the Verso
parser and quotations produce. Views expose one level of this structure at a time as ordinary Lean
datatypes. Each view node records the syntax it represents, the delimiter atoms that tooling such as
semantic highlighting needs, and decoded values for literal content. Using views allows clients to
avoid needing to check for things like optional brackets at all sites.

An `of` function returns `none` when the syntax does not have the specified shape. The parser and
quotations produce only well-formed trees, so a `none` result indicates a bug. Callers report it as
an error at the syntax in question.
-/

/--
A view of the value of an argument to a role, directive, command, or code block.
-/
inductive ArgValView where
  /-- A string literal. `value` is its decoded contents. -/
  | str (lit : StrLit) (value : String)
  /-- An identifier. -/
  | name (x : Ident)
  /-- A numeric literal. `value` is its decoded value. -/
  | num (lit : NumLit) (value : Nat)

/--
A view of `stx`, if it is an argument value.
-/
def ArgValView.of (stx : TSyntax ``Parser.argVal) : Option ArgValView :=
  match stx with
  | `(Parser.ArgVal.ident| $x:ident) => some (.name x)
  | `(Parser.ArgVal.num| $n:num) => some (.num n n.getNat)
  | `(Parser.ArgVal.str| $s:str) => some (.str s s.getString)
  | _ => none

/--
A view of an argument to a role, directive, command, or code block.
-/
inductive ArgView where
  /-- An anonymous positional argument. -/
  | anon (stx : TSyntax ``Parser.arg)
      (val : TSyntax ``Parser.argVal)
  /--
  A named argument. `parens` is the pair of parenthesis atoms when the argument is written in
  parentheses, and `assign` is the `:=` atom.
  -/
  | named (stx : TSyntax ``Parser.arg)
      (parens : Option (Syntax × Syntax)) (name : Ident) (assign : Syntax)
      (val : TSyntax ``Parser.argVal)
  /-- A flag. `sign` is the `+` or `-` atom, and `isOn` indicates which one it is. -/
  | flag (stx : TSyntax ``Parser.arg) (sign : Syntax) (name : Ident)
      (isOn : Bool)

/--
Returns the syntax underlying an argument view.
-/
def ArgView.stx : ArgView → TSyntax ``Parser.arg
  | .anon stx .. | .named stx .. | .flag stx .. => stx

/--
A view of `stx`, if it is an argument.
-/
def ArgView.of (stx : TSyntax ``Parser.arg) : Option ArgView :=
  match stx with
  | `(Parser.Arg.anon| $v:argVal) => some (.anon stx v)
  | `(Parser.Arg.named| (%$po $x:ident :=%$eq $v:argVal )%$pc) =>
    some (.named stx (some (po, pc)) x eq v)
  | `(Parser.Arg.named_no_paren| $x:ident :=%$eq $v:argVal) => some (.named stx none x eq v)
  | `(Parser.Arg.flag_on| +%$tk $x:ident) => some (.flag stx tk x true)
  | `(Parser.Arg.flag_off| -%$tk $x:ident) => some (.flag stx tk x false)
  | _ => none

/--
A view of a link target, which is either a URL or a reference to a URL defined elsewhere.
-/
inductive LinkTargetView where
  /-- A URL written directly, in parentheses. Use `TSyntax.getVersoLinkUrl` to read it. -/
  | url (stx : TSyntax ``Parser.linkTarget) (opener : Syntax)
      (url : VersoLinkUrl) (closer : Syntax)
  /--
  A reference to a URL defined elsewhere, in square brackets. Use `TSyntax.getVersoRefName` to read
  the name.
  -/
  | ref (stx : TSyntax ``Parser.linkTarget) (opener : Syntax)
      (name : VersoRefName) (closer : Syntax)

/--
Source info for a literal content token that stands in for a string literal written in a quotation.
The token the content came from supplies the positions and the canonicality. In macro-generated
syntax the positions do not point at the content, and code that reparses content relies on that
difference.
-/
private def decodedInfo (tok : Syntax) : SourceInfo :=
  match tok.getHeadInfo, tok.getPos?, tok.getTailPos? with
  | .original leading _ trailing _, some b, some e =>
    .original { leading with startPos := b, stopPos := b } b
      { trailing with startPos := e, stopPos := e } e
  | .synthetic _ _ canonical, some b, some e => .synthetic b e (canonical := canonical)
  | _, _, _ => .none

/--
Builds a string literal whose contents are `value`, positioned at the literal content token `tok` it
was decoded from. Reparsing content goes through a string literal, which carries the positions
that the parse reports against.
-/
def strLitOfContent (value : String) (tok : Syntax) : StrLit :=
  Syntax.mkStrLit value (info := decodedInfo tok)

/--
Creates source info for the content of empty code blocks.

A code block contains a sequence of lines. When that sequence is empty, the code block denotes the
empty string, which sits immediately before the code block's closing fence (here, `tok`).
-/
private def emptyContentInfo (tok : Syntax) : SourceInfo :=
  match tok.getHeadInfo, tok.getPos? with
  | .original leading _ _ _, some b =>
    .original { leading with startPos := b, stopPos := b } b
      { leading with startPos := b, stopPos := b } b
  | .synthetic _ _ canonical, some b => .synthetic b b (canonical := canonical)
  | _, _ => .none

/--
Escapes `value` so that `TSyntax.getVersoText` reads it back unchanged. Only the escape character
itself needs escaping, since decoding drops the backslash from any pair.
-/
private def escapeVersoText (value : String) : String :=
  value.foldl (init := "") fun out c => if c == '\\' then out ++ "\\\\" else out.push c


/--
Builds a text content token containing `value`, with its position taken from `src`.
-/
def mkVersoTextFrom (src : Syntax) (value : String) (canonical := false) : VersoText :=
  ⟨Syntax.mkLit versoTextKind (escapeVersoText value) (info := SourceInfo.fromRef src canonical)⟩

/--
Builds the name of a footnote or link reference containing `value`, with its position taken from
`src`.
-/
def mkVersoRefNameFrom (src : Syntax) (value : String) (canonical := false) : VersoRefName :=
  ⟨Syntax.mkLit versoRefKind value (info := SourceInfo.fromRef src canonical)⟩

/-- Builds a link URL token containing `value`, with its position taken from `src`. -/
def mkVersoLinkUrlFrom (src : Syntax) (value : String) (canonical := false) : VersoLinkUrl :=
  ⟨Syntax.mkLit versoLinkUrlKind (escapeVersoLinkUrl value)
    (info := SourceInfo.fromRef src canonical)⟩

/-- Builds an image's alternate text containing `value`, with its position taken from `src`. -/
def mkVersoImageAltFrom (src : Syntax) (value : String) (canonical := false) : VersoImageAlt :=
  ⟨Syntax.mkLit versoImageAltKind (escapeVersoImageAlt value)
    (info := SourceInfo.fromRef src canonical)⟩

/--
Builds the URL of a link reference definition containing `value`, with its position taken from
`src`.
-/
def mkVersoLinkRefUrlFrom (src : Syntax) (value : String) (canonical := false) : VersoLinkRefUrl :=
  ⟨Syntax.mkLit versoLinkRefUrlKind value (info := SourceInfo.fromRef src canonical)⟩

/--
Builds one `versoCodeLine` token per line of `value`, each containing its line through its newline,
all positioned by `info`. An empty value is one empty line.
-/
private def codeLinesFrom (info : SourceInfo) (value : String) : Array Syntax := Id.run do
  let mut lines := #[]
  let mut line := ""
  for c in value do
    line := line.push c
    if c == '\n' then
      lines := lines.push (Syntax.mkLit versoCodeLineKind line (info := info))
      line := ""
  if !line.isEmpty || lines.isEmpty then
    lines := lines.push (Syntax.mkLit versoCodeLineKind line (info := info))
  return lines

/--
Builds inline code content containing `value`, with one line token per line and its position taken
from `src`.
-/
def mkVersoCodeFrom (src : Syntax) (value : String) (canonical := false) : VersoCode :=
  let info := SourceInfo.fromRef src canonical
  ⟨Syntax.node info versoCodeKind #[mkNullNode (codeLinesFrom info value)]⟩

/--
Builds a code block's content containing `value`, with one line token per line and its position
taken from `src`.
-/
def mkVersoCodeBlockFrom (src : Syntax) (value : String) (canonical := false) : VersoCodeBlock :=
  let info := SourceInfo.fromRef src canonical
  ⟨Syntax.node info versoCodeBlockKind #[mkNullNode (codeLinesFrom info value)]⟩

/--
Builds a line break, with its position taken from `src`.
-/
def mkVersoLinebreakFrom (src : Syntax) (canonical := false) :
    TSyntax ``Parser.Inline.linebreak :=
  let info := SourceInfo.fromRef src canonical
  ⟨Syntax.node info ``Parser.Inline.linebreak #[.atom info "\n"]⟩

/-- Builds a line break, positioned at the current reference. -/
def mkVersoLinebreakFromRef [Monad m] [MonadRef m] (canonical := false) :
    m (TSyntax ``Parser.Inline.linebreak) := do
  return mkVersoLinebreakFrom (← getRef) canonical

/-- Builds a text content token containing `value`, positioned at the current reference. -/
def mkVersoTextFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoText := do
  return mkVersoTextFrom (← getRef) value canonical

/-- Builds a reference name containing `value`, positioned at the current reference. -/
def mkVersoRefNameFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoRefName := do
  return mkVersoRefNameFrom (← getRef) value canonical

/-- Builds a link URL containing `value`, positioned at the current reference. -/
def mkVersoLinkUrlFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoLinkUrl := do
  return mkVersoLinkUrlFrom (← getRef) value canonical

/-- Builds an image's alternate text containing `value`, positioned at the current reference. -/
def mkVersoImageAltFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoImageAlt := do
  return mkVersoImageAltFrom (← getRef) value canonical

/--
Builds the URL of a link reference definition containing `value`, positioned at the syntax `getRef`
returns.
-/
def mkVersoLinkRefUrlFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoLinkRefUrl := do
  return mkVersoLinkRefUrlFrom (← getRef) value canonical

/-- Builds inline code content containing `value`, positioned at the current reference. -/
def mkVersoCodeFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoCode := do
  return mkVersoCodeFrom (← getRef) value canonical

/-- Builds a code block's content containing `value`, positioned at the current reference. -/
def mkVersoCodeBlockFromRef [Monad m] [MonadRef m] (value : String) (canonical := false) :
    m VersoCodeBlock := do
  return mkVersoCodeBlockFrom (← getRef) value canonical

/--
A view of `stx`, if it is a link target.
-/
def LinkTargetView.of (stx : TSyntax ``Parser.linkTarget) : Option LinkTargetView :=
  match stx with
  | `(Parser.LinkTarget.url| (%$o $url:versoLinkUrl )%$c) => some (.url stx o url c)
  | `(Parser.LinkTarget.ref| [%$o $name:versoRef ]%$c) => some (.ref stx o name c)
  | _ => none

/--
A view of ordinary text.
-/
structure TextView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The text. -/
  content : VersoText
deriving Inhabited

/-- Decodes the Verso text contained in the view, interpreting escape sequences. -/
def TextView.getVersoText (v : TextView) : String := v.content.getVersoText

/--
Returns the literal representation of the text in the view, without interpreting escape sequences.
-/
def TextView.getVersoTextSource (v : TextView) : String := v.content.getVersoTextSource

/-- A view of `stx`, if it is ordinary text. -/
def TextView.of (stx : TSyntax ``Parser.inline) : Option TextView :=
  match stx with
  | `(Parser.Inline.text| $s:versoText) => some { stx, content := s }
  | _ => none

/--
A view of emphasized content.
-/
structure EmphView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of `_`. -/
  opener : TSyntax ``Parser.emphDelimiter
  /-- The emphasized content. -/
  content : TSyntaxArray ``Parser.inline
  /-- The closing run of `_`. -/
  closer : TSyntax ``Parser.emphDelimiter

/-- A view of `stx`, if it is emphasized content. -/
def EmphView.of (stx : TSyntax ``Parser.inline) : Option EmphView :=
  match stx with
  | `(Parser.Inline.emph| $o:emphDelimiter $inl* $c:emphDelimiter) =>
    some { stx, opener := o, content := inl, closer := c }
  | _ => none

/--
A view of bold content.
-/
structure BoldView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of `*`. -/
  opener : TSyntax ``Parser.boldDelimiter
  /-- The bold content. -/
  content : TSyntaxArray ``Parser.inline
  /-- The closing run of `*`. -/
  closer : TSyntax ``Parser.boldDelimiter

/-- A view of `stx`, if it is bold content. -/
def BoldView.of (stx : TSyntax ``Parser.inline) : Option BoldView :=
  match stx with
  | `(Parser.Inline.bold| $o:boldDelimiter $inl* $c:boldDelimiter) =>
    some { stx, opener := o, content := inl, closer := c }
  | _ => none

/--
A view of literal code.

This view is used both for inline code elements and the body of math notation.
-/
structure CodeView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The opening run of backticks. -/
  opener : TSyntax ``Parser.codeDelimiter
  /-- The code. -/
  content : VersoCode
  /-- The closing run of backticks. -/
  closer : TSyntax ``Parser.codeDelimiter

/-- The decoded code contents -/
def CodeView.getVersoCode (v : CodeView) : String := v.content.getVersoCode

/-- A view of `stx`, if it is inline code. -/
def CodeView.of (stx : TSyntax ``Parser.inline) : Option CodeView :=
  match stx with
  | `(Parser.Inline.code| $o:codeDelimiter $s:versoCode $c:codeDelimiter) =>
    some { stx, opener := o, content := s, closer := c }
  | _ => none

/--
A view of math content.
-/
structure MathView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- Whether the mathematics should be typeset in inline or display mode. -/
  mode : MathMode
  /-- The `$` or `$$` marker. -/
  marker : TSyntax [``Parser.inlineMathMarker, ``Parser.displayMathMarker]
  /-- The LaTeX-style math code. -/
  code : CodeView

/-- The decoded code contents. -/
def MathView.getVersoCode (v : MathView) : String := v.code.getVersoCode

/--
A view of `stx`, if it is math content.

Math nests a code element, so the view contains the view of that element.
-/
def MathView.of (stx : TSyntax ``Parser.inline) : Option MathView := do
  match stx with
  | `(Parser.Inline.inline_math| $m:inlineMathMarker $c:code) =>
    return { stx, mode := .inline, marker := m, code := ← CodeView.of ⟨c.raw⟩ }
  | `(Parser.Inline.display_math| $m:displayMathMarker $c:code) =>
    return { stx, mode := .display, marker := m, code := ← CodeView.of ⟨c.raw⟩ }
  | _ => none

/--
A view of a link.
-/
structure LinkView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `[` that opens the link text. -/
  opener : Syntax
  /-- The link text. -/
  content : TSyntaxArray ``Parser.inline
  /-- The `]` that closes the link text. -/
  closer : Syntax
  /-- Where the link leads. -/
  target : LinkTargetView

/-- A view of `stx`, if it is a link. -/
def LinkView.of (stx : TSyntax ``Parser.inline) : Option LinkView := do
  match stx with
  | `(Parser.Inline.link| [%$o $inl* ]%$c $tgt:linkTarget) =>
    return { stx, opener := o, content := inl, closer := c, target := ← LinkTargetView.of tgt }
  | _ => none

/--
A view of an image.
-/
structure ImageView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `![` that opens the alternate text. -/
  opener : Syntax
  /-- The alternate text. -/
  alt : VersoImageAlt
  /-- The `]` that closes the alternate text. -/
  closer : Syntax
  /-- Where the image is found. -/
  target : LinkTargetView

/-- The alternate text, with each escape replaced by the character it denotes. -/
def ImageView.getAlt (v : ImageView) : String := v.alt.getVersoImageAlt

/-- A view of `stx`, if it is an image. -/
def ImageView.of (stx : TSyntax ``Parser.inline) : Option ImageView := do
  match stx with
  | `(Parser.Inline.image| ![%$o $alt:versoImageAlt ]%$c $tgt:linkTarget) =>
    return { stx, opener := o, alt, closer := c, target := ← LinkTargetView.of tgt }
  | _ => none

/--
A view of a footnote use site.
-/
structure FootnoteView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `[^` that opens the name. -/
  opener : Syntax
  /-- The name that refers to the footnote's definition. -/
  name : VersoRefName
  /-- The `]` that closes the name. -/
  closer : Syntax

/-- The name that refers to the footnote's definition. -/
def FootnoteView.getName (v : FootnoteView) : String := v.name.getVersoRefName

/-- A view of `stx`, if it is a footnote use site. -/
def FootnoteView.of (stx : TSyntax ``Parser.inline) : Option FootnoteView :=
  match stx with
  | `(Parser.Inline.footnote| [^%$o $name:versoRef ]%$c) =>
    some { stx, opener := o, name, closer := c }
  | _ => none

/--
A view of a line break.
-/
structure LinebreakView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The newline atom. -/
  newline : Syntax

/-- A view of `stx`, if it is a line break. -/
def LinebreakView.of (stx : TSyntax ``Parser.inline) : Option LinebreakView :=
  match stx with
  | `(Parser.Inline.linebreak| $nl:linebreak) => some { stx, newline := nl.raw[0] }
  | _ => none

/--
A view of content with a role.
-/
structure RoleView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.inline
  /-- The `{` that opens the name and arguments. -/
  braceOpen : Syntax
  /-- The name that selects the role's expander. -/
  name : Ident
  /-- The arguments to the role. -/
  args : TSyntaxArray ``Parser.arg
  /-- The `}` that closes the name and arguments. -/
  braceClose : Syntax
  /--
  The brackets around the content, if they are present.
  -/
  brackets : Option (Syntax × Syntax)
  /-- The content that the role applies to. -/
  content : TSyntaxArray ``Parser.inline

/--
A view of `stx`, if it is content with a role.

An author may write content that has delimiters of its own without brackets, so the brackets are
matched separately from the name and arguments.
-/
def RoleView.of (stx : TSyntax ``Parser.inline) : Option RoleView :=
  match stx with
  | `(Parser.Inline.role| {%$bo $name:ident $args* }%$bc [%$so $inl* ]%$sc) =>
    some {
      stx, braceOpen := bo, name, args, braceClose := bc,
      brackets := some (so, sc), content := inl
    }
  | `(Parser.Inline.role| {%$bo $name:ident $args* }%$bc $inl:inline*) =>
    some {
      stx, braceOpen := bo, name, args, braceClose := bc,
      brackets := none, content := inl
    }
  | _ => none

/--
A view of an inline document element.
-/
inductive InlineView where
  /-- Ordinary text. -/
  | text (view : TextView)
  /-- Emphasized content. -/
  | emph (view : EmphView)
  /-- Bold content. -/
  | bold (view : BoldView)
  /-- Literal code. -/
  | code (view : CodeView)
  /-- Mathematical notation. -/
  | math (view : MathView)
  /-- A link. -/
  | link (view : LinkView)
  /-- An image. -/
  | image (view : ImageView)
  /-- A footnote use site. -/
  | footnote (view : FootnoteView)
  /-- A soft line break. -/
  | linebreak (view : LinebreakView)
  /-- A role applied to some content. -/
  | role (view : RoleView)
deriving Inhabited

instance : Coe TextView InlineView := ⟨.text⟩
instance : Coe EmphView InlineView := ⟨.emph⟩
instance : Coe BoldView InlineView := ⟨.bold⟩
instance : Coe CodeView InlineView := ⟨.code⟩
instance : Coe MathView InlineView := ⟨.math⟩
instance : Coe LinkView InlineView := ⟨.link⟩
instance : Coe ImageView InlineView := ⟨.image⟩
instance : Coe FootnoteView InlineView := ⟨.footnote⟩
instance : Coe LinebreakView InlineView := ⟨.linebreak⟩
instance : Coe RoleView InlineView := ⟨.role⟩

/--
Returns the original syntax that an inline view was constructed from.
-/
def InlineView.stx : InlineView → TSyntax ``Parser.inline
  | .text v => v.stx
  | .emph v => v.stx
  | .bold v => v.stx
  | .code v => v.stx
  | .math v => v.stx
  | .link v => v.stx
  | .image v => v.stx
  | .footnote v => v.stx
  | .linebreak v => v.stx
  | .role v => v.stx

/--
A view of `stx`, if it is an inline document element.

Each production has a view of its own, and this tries them in turn. The productions have distinct
syntax kinds, so at most one applies and the order does not matter.
-/
def InlineView.of (stx : TSyntax ``Parser.inline) : Option InlineView :=
  .text <$> TextView.of stx <|>
  .emph <$> EmphView.of stx <|>
  .bold <$> BoldView.of stx <|>
  .code <$> CodeView.of stx <|>
  .math <$> MathView.of stx <|>
  .link <$> LinkView.of stx <|>
  .image <$> ImageView.of stx <|>
  .footnote <$> FootnoteView.of stx <|>
  .linebreak <$> LinebreakView.of stx <|>
  .role <$> RoleView.of stx

/--
A view of an item of an unordered list.
-/
structure UnorderedListItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.ListItem.item
  /-- The marker, which is `*`, `-`, or `+`. -/
  marker : TSyntax ``Parser.listMarker
  /-- The item's contents. -/
  contents : TSyntaxArray ``Parser.block

/--
A view of `stx`, if it is an unordered list's item. Its marker must be a bullet.
-/
def UnorderedListItemView.of (stx : TSyntax ``Parser.ListItem.item) :
    Option UnorderedListItemView :=
  match stx with
  | `(Parser.ListItem.item| $m:listMarker $bs*) =>
    if m.getVersoDelimiter.front? |>.any (· ∈ ['*', '-', '+']) then some ⟨stx, m, bs⟩ else none
  | _ => none

/--
A view of an item of an ordered list.
-/
structure OrderedListItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.ListItem.item
  /-- The marker, which is a number followed by `.` or `)`. -/
  marker : TSyntax ``Parser.listMarker
  /-- The item's contents. -/
  contents : TSyntaxArray ``Parser.block

/-- The number that the item's marker gives it. -/
def OrderedListItemView.number (v : OrderedListItemView) : Option Nat :=
  v.marker.getVersoDelimiter.takeWhile (·.isDigit) |>.copy.toNat?

/--
A view of `stx`, if it is an ordered list's item. Its marker must be a number.
-/
def OrderedListItemView.of (stx : TSyntax ``Parser.ListItem.item) : Option OrderedListItemView :=
  match stx with
  | `(Parser.ListItem.item| $m:listMarker $bs*) =>
    if m.getVersoDelimiter.front? |>.any (·.isDigit) then some ⟨stx, m, bs⟩ else none
  | _ => none

/--
A view of an item description from a description list.
-/
structure DescItemView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.DescItem.item
  /-- The `:` that introduces the item. -/
  marker : Syntax
  /-- The term that the item describes. -/
  term : TSyntaxArray ``Parser.inline
  /-- The description. -/
  desc : TSyntaxArray ``Parser.block

/--
A view of `stx`, if it is a description list item.
-/
def DescItemView.of (stx : TSyntax ``Parser.DescItem.item) : Option DescItemView :=
  match stx with
  | `(Parser.DescItem.item| :%$marker $term:inline* $desc:block*) =>
    some ⟨stx, marker, term, desc⟩
  | _ => none

/--
A view of a paragraph.
-/
structure ParaView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The paragraph's contents. -/
  content : TSyntaxArray ``Parser.inline
deriving Inhabited

/-- A view of `stx`, if it is a paragraph. -/
def ParaView.of (stx : TSyntax ``Parser.block) : Option ParaView :=
  match stx with
  | `(Parser.Block.para| $inl*) => some { stx, content := inl }
  | _ => none

/--
A view of an unordered list.
-/
structure UnorderedListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The list's items. -/
  items : Array UnorderedListItemView

/-- A view of `stx`, if it is an unordered list. -/
def UnorderedListView.of (stx : TSyntax ``Parser.block) : Option UnorderedListView := do
  match stx with
  | `(Parser.Block.ul| $items:ListItem.item*) =>
    return { stx, items := ← items.mapM UnorderedListItemView.of }
  | _ => none

/--
A view of an ordered list.
-/
structure OrderedListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The number of the first item, which the first item's marker gives it. -/
  start : Nat
  /-- The list's items. -/
  items : Array OrderedListItemView

/-- A view of `stx`, if it is an ordered list. -/
def OrderedListView.of (stx : TSyntax ``Parser.block) : Option OrderedListView := do
  match stx with
  | `(Parser.Block.ol| $items:ListItem.item*) =>
    let items ← items.mapM OrderedListItemView.of
    return { stx, start := items[0]?.bind (·.number) |>.getD 1, items }
  | _ => none

/--
A view of a description list.
-/
structure DescListView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The list's items. -/
  items : Array DescItemView

/-- A view of `stx`, if it is a description list. -/
def DescListView.of (stx : TSyntax ``Parser.block) : Option DescListView := do
  match stx with
  | `(Parser.Block.dl| $items:DescItem.item*) =>
    return { stx, items := ← items.mapM DescItemView.of }
  | _ => none

/--
A view of a block quotation.
-/
structure BlockquoteView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `>` that introduces the quotation. -/
  marker : Syntax
  /-- The quoted blocks. -/
  content : TSyntaxArray ``Parser.block

/-- A view of `stx`, if it is a block quotation. -/
def BlockquoteView.of (stx : TSyntax ``Parser.block) : Option BlockquoteView :=
  match stx with
  | `(Parser.Block.blockquote| >%$gt $bs*) => some { stx, marker := gt, content := bs }
  | _ => none

/--
A view of a code block.
-/
structure CodeBlockView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening run of backticks. -/
  openFence : TSyntax ``Parser.codeBlockFence
  /-- The name that selects the code block's expander, where the code block invokes one. -/
  name? : Option Ident
  /-- The arguments to the expander. -/
  args : TSyntaxArray ``Parser.arg
  /-- The code. -/
  content : VersoCodeBlock
  /-- The closing run of backticks. -/
  closeFence : TSyntax ``Parser.codeBlockFence

/-- The code, which is the texts of its lines in order. -/
def CodeBlockView.getVersoCodeBlock (v : CodeBlockView) : String := v.content.getVersoCodeBlock

/-- A view of `stx`, if it is a code block. -/
def CodeBlockView.of (stx : TSyntax ``Parser.block) : Option CodeBlockView :=
  match stx with
  | `(Parser.Block.codeblock| $openFence:codeBlockFence $[$name:ident $args*]? $s:versoCodeBlock
        $closeFence:codeBlockFence) =>
    -- Empty content parses with no tokens of its own, so its location is the closing fence.
    let content : VersoCodeBlock :=
      if s.raw.getPos?.isSome then s else ⟨s.raw.setInfo (emptyContentInfo closeFence)⟩
    some {
      stx, openFence, name? := name, args := args.getD #[], content, closeFence
    }
  | _ => none

/--
A view of a directive.
-/
structure DirectiveView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening run of colons. -/
  opener : TSyntax ``Parser.directiveDelimiter
  /-- The name that selects the directive's expander. -/
  name : Ident
  /-- The arguments to the directive. -/
  args : TSyntaxArray ``Parser.arg
  /-- The blocks that the directive contains. -/
  content : TSyntaxArray ``Parser.block
  /-- The closing run of colons. -/
  closer : TSyntax ``Parser.directiveDelimiter

/-- A view of `stx`, if it is a directive. -/
def DirectiveView.of (stx : TSyntax ``Parser.block) : Option DirectiveView :=
  match stx with
  | `(Parser.Block.directive| $opener:directiveDelimiter $name:ident $args:arg* $bs:block*
        $closer:directiveDelimiter) =>
    some { stx, opener, name, args, content := bs, closer }
  | _ => none

/--
A view of a block-level command.
-/
structure CommandView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `{` that opens the name and arguments. -/
  braceOpen : Syntax
  /-- The name that selects the command's expander. -/
  name : Ident
  /-- The arguments to the command. -/
  args : TSyntaxArray ``Parser.arg
  /-- The `}` that closes the name and arguments. -/
  braceClose : Syntax

/-- A view of `stx`, if it is a block-level command. -/
def CommandView.of (stx : TSyntax ``Parser.block) : Option CommandView :=
  match stx with
  | `(Parser.Block.command| {%$braceOpen $name:ident $args* }%$braceClose) =>
    some { stx, braceOpen, name, args, braceClose }
  | _ => none

/--
A view of a section header.
-/
structure HeaderView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The run of `#` characters. -/
  marker : TSyntax ``Parser.headerMarker
  /-- The header's nesting depth, with `0` denoting a top-level header. -/
  level : Nat
  /-- The header's text. -/
  content : TSyntaxArray ``Parser.inline

/-- A view of `stx`, if it is a section header. -/
def HeaderView.of (stx : TSyntax ``Parser.block) : Option HeaderView :=
  match stx with
  | `(Parser.Block.header| $marker:headerMarker $content*) =>
    -- The header's level is the length of the `#` run that the marker contains.
    some { stx, marker, level := marker.getVersoDelimiter.length - 1, content }
  | _ => none

/--
A view of a named URL that links and images can use.
-/
structure LinkRefView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `[` that opens the name. -/
  opener : Syntax
  /-- The name that a link or image uses to reach the URL. -/
  name : VersoRefName
  /-- The `]:` that closes the name. -/
  closer : Syntax
  /-- The URL. -/
  url : VersoLinkRefUrl

/-- The name that a link or image repeats to reach this URL. -/
def LinkRefView.getName (v : LinkRefView) : String := v.name.getVersoRefName

/-- The URL that the reference provides. -/
def LinkRefView.getUrl (v : LinkRefView) : String := v.url.getVersoLinkRefUrl

/-- A view of `stx`, if it is a named URL. -/
def LinkRefView.of (stx : TSyntax ``Parser.block) : Option LinkRefView :=
  match stx with
  | `(Parser.Block.link_ref| [%$opener $name:versoRef ]:%$closer $url:versoLinkRefUrl) =>
    some { stx, opener, name, closer, url }
  | _ => none

/--
A view of a footnote definition.
-/
structure FootnoteRefView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The `[^` that opens the name. -/
  opener : Syntax
  /-- The name of the footnote. -/
  name : VersoRefName
  /-- The `]:` that closes the name. -/
  closer : Syntax
  /-- The footnote's text. -/
  content : TSyntaxArray ``Parser.inline

/-- The name of the footnote. -/
def FootnoteRefView.getName (v : FootnoteRefView) : String := v.name.getVersoRefName

/-- A view of `stx`, if it is a footnote definition. -/
def FootnoteRefView.of (stx : TSyntax ``Parser.block) : Option FootnoteRefView :=
  match stx with
  | `(Parser.Block.footnote_ref| [^%$opener $name:versoRef ]:%$closer $content*) =>
    some { stx, opener, name, closer, content }
  | _ => none

/--
A view of a metadata block for the preceding header.
-/
structure MetadataView where
  /-- The original syntax. -/
  stx : TSyntax ``Parser.block
  /-- The opening `%%%`. -/
  opener : Syntax
  /-- The metadata, written as the fields of a Lean structure instance. -/
  contents : TSyntax ``Lean.Parser.Term.structInstFields
  /-- The closing `%%%`. -/
  closer : Syntax

/-- The individual metadata fields, without their separators. -/
def MetadataView.fields (v : MetadataView) :
    TSyntaxArray ``Lean.Parser.Term.structInstField :=
  v.contents.raw[0].getSepArgs.map (⟨·⟩)

/-- A view of `stx`, if it is a metadata block. -/
def MetadataView.of (stx : TSyntax ``Parser.block) : Option MetadataView :=
  match stx with
  | `(Parser.Block.metadata_block| %%%%$opener $contents:metadataContents %%%%$closer) =>
    some { stx, opener, contents, closer }
  | _ => none

/--
A view of a block-level document element.

Each view records the syntax it is a view of, the delimiter atoms, and decoded values for literal
content. Nested content stays as concrete syntax, for the consumer to view in turn.
-/
inductive BlockView where
  /-- A paragraph. -/
  | para (view : ParaView)
  /-- An unordered list. -/
  | ul (view : UnorderedListView)
  /-- An ordered list. -/
  | ol (view : OrderedListView)
  /-- A description list. -/
  | dl (view : DescListView)
  /-- A block quotation. -/
  | blockquote (view : BlockquoteView)
  /-- A code block. -/
  | codeblock (view : CodeBlockView)
  /-- A directive. -/
  | directive (view : DirectiveView)
  /-- A block-level command. -/
  | command (view : CommandView)
  /-- A section header. -/
  | header (view : HeaderView)
  /-- A named URL that links and images can use. -/
  | linkRef (view : LinkRefView)
  /-- A footnote definition. -/
  | footnoteRef (view : FootnoteRefView)
  /-- A metadata block for the preceding header. -/
  | metadata (view : MetadataView)
deriving Inhabited

instance : Coe ParaView BlockView := ⟨.para⟩
instance : Coe UnorderedListView BlockView := ⟨.ul⟩
instance : Coe OrderedListView BlockView := ⟨.ol⟩
instance : Coe DescListView BlockView := ⟨.dl⟩
instance : Coe BlockquoteView BlockView := ⟨.blockquote⟩
instance : Coe CodeBlockView BlockView := ⟨.codeblock⟩
instance : Coe DirectiveView BlockView := ⟨.directive⟩
instance : Coe CommandView BlockView := ⟨.command⟩
instance : Coe HeaderView BlockView := ⟨.header⟩
instance : Coe LinkRefView BlockView := ⟨.linkRef⟩
instance : Coe FootnoteRefView BlockView := ⟨.footnoteRef⟩
instance : Coe MetadataView BlockView := ⟨.metadata⟩

/--
Returns the syntax underlying a block view.
-/
def BlockView.stx : BlockView → TSyntax ``Parser.block
  | .para v => v.stx
  | .ul v => v.stx
  | .ol v => v.stx
  | .dl v => v.stx
  | .blockquote v => v.stx
  | .codeblock v => v.stx
  | .directive v => v.stx
  | .command v => v.stx
  | .header v => v.stx
  | .linkRef v => v.stx
  | .footnoteRef v => v.stx
  | .metadata v => v.stx

/--
A view of `stx`, if it is a block-level document element.

Each production has a view of its own, and this tries them in turn. The productions have distinct
syntax kinds, so at most one applies and the order does not matter.
-/
def BlockView.of (stx : TSyntax ``Parser.block) : Option BlockView :=
  .para <$> ParaView.of stx <|>
  .ul <$> UnorderedListView.of stx <|>
  .ol <$> OrderedListView.of stx <|>
  .dl <$> DescListView.of stx <|>
  .blockquote <$> BlockquoteView.of stx <|>
  .codeblock <$> CodeBlockView.of stx <|>
  .directive <$> DirectiveView.of stx <|>
  .command <$> CommandView.of stx <|>
  .header <$> HeaderView.of stx <|>
  .linkRef <$> LinkRefView.of stx <|>
  .footnoteRef <$> FootnoteRefView.of stx <|>
  .metadata <$> MetadataView.of stx

/--
Returns a view of an inline element of a Verso document.

Returns `default` if the syntax is malformed.
-/
def VersoInline.view (stx : VersoInline) : InlineView := (InlineView.of stx).getD default

/--
Returns a view of a block-level element of a Verso document.

Returns `default` if the syntax is malformed.
-/
def VersoBlock.view (stx : VersoBlock) : BlockView := (BlockView.of stx).getD default

section Migration
/-
The wrappers that documentation extensions are given carry their content under the tags that the
stage0 which generated them uses, and the functions below present it under the types a declaration
names. Inline and block content is already the parser's syntax, so those two are retaggings. After
a stage0 update a wrapper receives the content directly, and this section can be deleted.
-/

/-- Retags inline content that a wrapper received. -/
def migrateInlines (xs : TSyntaxArray `inline) : TSyntaxArray ``Parser.inline :=
  TSyntaxArray.mk xs.raw

/-- Retags block content that a wrapper received. -/
def migrateBlocks (xs : TSyntaxArray `block) : TSyntaxArray ``Parser.block :=
  TSyntaxArray.mk xs.raw

/-- Presents a string literal's contents as an inline code content token. -/
def versoCodeOfStrLit (s : StrLit) : VersoCode := mkVersoCodeFrom s s.getString

/-- Presents a string literal's contents as a code block content token. -/
def versoCodeBlockOfStrLit (s : StrLit) : VersoCodeBlock := mkVersoCodeBlockFrom s s.getString

end Migration

end
