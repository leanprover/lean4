/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
import Init.Prelude
public meta import Init.Data.Sum.Basic
public meta import Init.Data.String.Modify
public meta import Lean.Meta.Hint
public meta import Lean.Data.Html.Spec
public meta import Lean.Data.Html.Entities

set_option doc.verso true

public meta section

namespace Lean.Html.Syntax

open Parser PrettyPrinter

/-! # Parsers for HTML syntax

- Compliant with the [HTML living standard](https://html.spec.whatwg.org/dev/syntax.html#syntax)
  to the extent that it makes sense.
  Departures are documented on the appropriate parsers.
- We eschew Lean's standard mechanism of syntactic categories
  in favor of hand-rolled parsers, formatters, and parenthesizers for two reasons:
  - Lean parsers generally consume trailing whitespace,
    whereas certain HTML parsers (e.g. end tag `>` symbols) should not do so,
    so that this whitespace is instead included in text content following those parsers.
  - Category parsing inspects the leading token and dispatches to the appropriate parser
    whereas we allow text contents to begin with reserved symbols such as `'`.
- In content, all whitespace is preserved by parsers, and then collapsed in {lit}`Content.view`.
- To simplify away special handling of `$`, most parsers here cannot be antiquoted.
  Parsers that *can* be antiquoted are documented as such.
-/

/-! ## Helpers -/

/-- Consumes one character satisfying {name}`p`,
otherwise fails and reports the unexpected character. -/
private def satisfyCharFn (p : Char → Bool) (expected : List String) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s.mkEOIError expected
  else if p (c.get' i h) then
    s.next' c i h
  else
    s.mkUnexpectedError s!"unexpected character '{c.get' i h}'" expected

/-- Parses one character matching {name}`firstP` followed by many matching {name}`manyP`,
followed by optional trailing whitespace (including Lean-language comments).
The result is stored in an atom wrapped in a node of the given {name}`kind`.
{name}`expected` describes the expected input in error messages. -/
private def parseFirstMany (kind : Name) (expected : String) (firstP manyP : Char → Bool) :
    Parser where
  fn c s :=
    let startPos := s.pos
    let s := andthenFn (satisfyCharFn firstP [expected]) (takeWhileFn manyP) c s
    mkNodeToken kind startPos (includeWhitespace := true) c s

@[combinator_parenthesizer parseFirstMany]
private def parseFirstMany.parenthesizer (_ : Name) (_ : String) (_ _ : Char → Bool) :=
  Parenthesizer.visitToken

@[combinator_formatter parseFirstMany]
private def parseFirstMany.formatter (kind : Name) (_ : String) (_ _ : Char → Bool) :=
  Formatter.visitAtom kind

private def viewNodeAtom [Monad m] [MonadError m] : TSyntax k → m String
  | ⟨.node _ _ #[.atom _ s]⟩ => return s
  | _ => Elab.throwUnsupportedSyntax

/-- Syntax spanning bytes {name}`b` to {name}`e` of {name}`s`, for reporting errors. -/
private def subsyntaxNodeAtom (s : Syntax) (b e : String.Pos.Raw) : Syntax :=
  match s with
  | .node _ _ #[.atom (.original _ pos _ _) s] =>
    .atom (.synthetic ⟨pos.byteIdx + b.byteIdx⟩ ⟨pos.byteIdx + e.byteIdx⟩ (canonical := true))
      (b.extract s e)
  | _ => s

/-! ## Character references -/

/-- Returns the string encoded by the body {lit}`ref` of an
[HTML character reference](https://html.spec.whatwg.org/dev/syntax.html#character-references)
{lit}`&ref;`,
or {name}`none` if the body is invalid.

Named references (such as {lit}`&amp;`) must be listed in the HTML standard.
Numeric references in decimal ({lit}`&#123;`) or hexadecimal ({lit}`&#x7B;`) notation
must denote a Unicode scalar value that is not U+0000, U+000D,
a noncharacter, or a control other than ASCII whitespace. -/
def characterReference? (ref : String) : Option String :=
  let i : String.Pos.Raw := 0
  if h : i.atEnd ref then none
  else if i.get' ref h == '#' then
    let i := i.next' ref h
    if h : i.atEnd ref then none
    else if i.get' ref h == 'x' || i.get' ref h == 'X' then numeric 16 ref (i.next' ref h)
    else numeric 10 ref i
  else namedCharacterReference? ref
where
  numeric (radix : Nat) (ref : String) (i : String.Pos.Raw) : Option String := do
    let mut n : Nat := 0
    let mut i := i
    while h : ¬i.atEnd ref do
      let d ← digit? (i.get' ref h)
      if d ≥ radix then none
      n := n * radix + d
      if n > 0x10FFFF then none -- exceeded Unicode range
      i := i.next' ref h
    let c := Char.ofNat n
    if c == '\x00' || c == '\x0d' || isNonCharacter c || (isControl c && !isAsciiWhitespace c) then
      none
    return String.singleton c
  digit? (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (10 + c.toNat - 'a'.toNat)
    else if 'A' ≤ c && c ≤ 'F' then some (10 + c.toNat - 'A'.toNat)
    else none

/-- Decodes one character reference starting at {name}`i`,
which must point at at the character {lit}`&` in {name}`s`.
Returns the decoded string, and the position just after {lit}`;`.

Errors are reported using {name}`errAt`,
which takes two offsets into {name}`s` and the error message. -/
partial def decodeCharacterReferenceAt [Monad m]
    (s : String) (i : String.Pos.Raw)
    (errAt : ∀ {α}, String.Pos.Raw → String.Pos.Raw → MessageData → m α) :
    m (String × String.Pos.Raw) := do
  -- The body is an optional `#` followed by at least one ASCII alphanumeric.
  let j := i.next s
  let k := if j.get s == '#' then j.next s else j
  let bodyEnd := skipAlphanum s k
  if bodyEnd.get s != ';' then
    errAt i bodyEnd m!"Unterminated HTML character reference '{i.extract s bodyEnd}'"
  let refEnd := bodyEnd.next s
  match characterReference? (j.extract s bodyEnd) with
  | some val => return (val, refEnd)
  | none =>
    let kind := if j.get s == '#' then "numeric" else "named"
    errAt i refEnd m!"Invalid HTML {kind} character reference `{i.extract s refEnd}`"
where
  skipAlphanum (s : String) (i : String.Pos.Raw) : String.Pos.Raw :=
    if h : i.atEnd s then i
    else if (i.get' s h).isAlphanum then skipAlphanum s (i.next' s h)
    else i

/-- Decodes HTML character references in {name}`ref`, leaving other characters unchanged. -/
partial def decodeCharacterReferences [Monad m] [MonadError m]
    (ref : TSyntax `str) : m String :=
  go ref.getString ⟨0⟩ ""
where
  go (s : String) (i : String.Pos.Raw) (out : String) : m String := do
    if h : i.atEnd s then
      return out
    else
      let c := i.get' s h
      if c == '&' then
        let (val, refEnd) ← decodeCharacterReferenceAt s i
          (fun s e m => throwErrorAt (subsyntaxNodeAtom ref ⟨s.byteIdx+1⟩ ⟨e.byteIdx+1⟩) m)
        go s refEnd (out ++ val)
      else
        go s (i.next' s h) (out.push c)

/-! ## Raw symbols -/

/-- Parses {name}`sym` as an atom.
Unlike {name}`symbol`, this parser does not consult the token table,
and {name}`sym` is not registered as a token.

Trailing whitespace (including Lean-style comments) is consumed and stored in the atom
only if {name}`trailingWs` is set; otherwise it is left to the next parser. -/
def rawSymbol (sym : String) (trailingWs := false) (expected : List String := [s!"'{sym}'"]) :
    Parser where
  fn := rawFn (trailingWs := trailingWs) fun c s =>
    let i := s.pos
    let j : String.Pos.Raw := ⟨i.byteIdx + sym.utf8ByteSize⟩
    if j.byteIdx ≤ c.endPos.byteIdx && c.extract i j == sym then
      s.setPos j
    else if h : c.atEnd i then
      s.mkEOIError expected
    else
      s.mkUnexpectedError s!"unexpected character '{c.get' i h}'" expected

@[combinator_parenthesizer rawSymbol]
def rawSymbol.parenthesizer (sym : String) (_ : Bool) (_ : List String) :=
  Parenthesizer.symbolNoAntiquot.parenthesizer sym

@[combinator_formatter rawSymbol]
def rawSymbol.formatter (sym : String) (_ : Bool) (_ : List String) : Formatter := do
  -- No space is inserted after the symbol.
  Formatter.resetLeadWord
  Formatter.symbolNoAntiquot.formatter sym

/-! ## Interpolations -/

/-- Parses an interpolation: a Lean term between {name}`openSym` and {lit}`}`.
Trailing whitespace is consumed only if {name}`trailingWs` is set. -/
@[run_parser_attribute_hooks]
def interpWith (kind : SyntaxNodeKind) (openSym : String) (trailingWs : Bool) : Parser :=
  node kind <|
    rawSymbol openSym (trailingWs := true) >> termParser >> rawSymbol "}" (trailingWs := trailingWs)

abbrev interpKind := `Lean.Html.Syntax.interp
abbrev interpManyKind := `Lean.Html.Syntax.interpMany

/-- Parses {lit}`{ term }`. -/
@[run_parser_attribute_hooks]
def interp (trailingWs : Bool := false) : Parser := interpWith interpKind "{" trailingWs

/-- Parses {lit}`{... term }`. -/
@[run_parser_attribute_hooks]
def interpMany (trailingWs : Bool := false) : Parser := interpWith interpManyKind "{..." trailingWs

/-! ## Text content -/

abbrev textKind := `Lean.Html.Syntax.text
abbrev Text := TSyntax textKind

/-- Parses [HTML text content](https://html.spec.whatwg.org/dev/dom.html#text-content),
stopping at an interpolation {lit}`{`, a tag `<`,
or a closing bracket `}` (for {lit}`html%{ text }`). -/
def text : Parser where
  fn c s :=
    let startPos := s.pos
    let s := takeWhile1Fn isTextChar "expected HTML text" c s
    mkNodeToken textKind startPos (includeWhitespace := false) c s
where
  isTextChar (c : Char) :=
    (!isControl c || isAsciiWhitespace c) && !isNonCharacter c && c ∉ ['{', '}', '<']

@[combinator_parenthesizer text, parenthesizer Lean.Html.Syntax.text]
def text.parenthesizer : Parenthesizer := Parenthesizer.visitToken

@[combinator_formatter text, formatter Lean.Html.Syntax.text]
def text.formatter : Formatter := Formatter.visitAtom textKind

/-- Accumulator for normalizing the contents of a run of {name}`text` nodes. -/
private structure TextAcc where
  out : String := ""
  /-- Whether whitespace occurred after the last append to {lit}`out`. -/
  pendingWs : Bool := false

namespace TextAcc

/-- Appends a single space whenever whitespace is pending,
except when {name}`trimStart` is set and we haven't seen any non-whitespace yet -
then pending whitespace is discarded. -/
private def flushWs (acc : TextAcc) (trimStart : Bool) : TextAcc :=
  let keep := acc.pendingWs && !(trimStart && acc.out.isEmpty)
  { acc with out := if keep then acc.out.push ' ' else acc.out, pendingWs := false }

/-- Returns the accumulated text.
Trailing whitespace is removed if {name}`trimEnd` is set. -/
private def finish (acc : TextAcc) (trimStart trimEnd : Bool) : String :=
  if trimEnd then acc.out else acc.flushWs trimStart |>.out

/-- Appends the text of {name}`t` to the accumulator,
normalizing as described in {lit}`Content.view`.
Whitespace at the start is dropped when {name}`trimStart` is set.
Throws if {name}`t` contains an invalid character reference. -/
private partial def push [Monad m] [MonadError m]
  (acc : TextAcc) (t : Text) (trimStart : Bool) : m TextAcc := do
  go (← viewNodeAtom t) ⟨0⟩ acc
where
  go (s : String) (i : String.Pos.Raw) (acc : TextAcc) : m TextAcc := do
    if i.atEnd s then
      return acc
    let c := i.get s
    let j := i.next s
    if isAsciiWhitespace c then
      go s j { acc with pendingWs := true }
    else
      let acc := acc.flushWs trimStart
      if c == '&' then
        let (val, refEnd) ← decodeCharacterReferenceAt s i
          (fun s e m => throwErrorAt (subsyntaxNodeAtom t s e) m)
        go s refEnd { acc with out := acc.out ++ val }
      else
        go s j { acc with out := acc.out.push c }

end TextAcc

/-! ## Comments -/

abbrev commentKind := `Lean.Html.Syntax.comment
abbrev Comment := TSyntax commentKind

private partial def commentContentsFn : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s.mkEOIError ["'-->' (end of HTML comment)"]
  else if c.get' i h == '-' && c.get ⟨i.byteIdx + 1⟩ == '-' then
    if c.get ⟨i.byteIdx + 2⟩ == '>' then
      s.setPos ⟨i.byteIdx + 3⟩
    else if c.get ⟨i.byteIdx + 2⟩ == '!' && c.get ⟨i.byteIdx + 3⟩ == '>' then
      s.mkUnexpectedError "HTML comment may not contain '--!>'"
    else
      commentContentsFn c (s.setPos (c.next' i h))
  else if c.get' i h == '<'
      && c.get ⟨i.byteIdx + 1⟩ == '!'
      && c.get ⟨i.byteIdx + 2⟩ == '-'
      && c.get ⟨i.byteIdx + 3⟩ == '-' then
    s.mkUnexpectedError "HTML comment may not contain '<!--'"
  else
    commentContentsFn c (s.setPos (c.next' i h))

/-- Consumes the start `<!--` of an HTML comment,
then continues with {name}`commentContentsFn`. -/
private partial def commentFn : ParserFn := fun c s =>
  let i := s.pos
  if c.get i != '<'
      || c.get ⟨i.byteIdx + 1⟩ != '!'
      || c.get ⟨i.byteIdx + 2⟩ != '-'
      || c.get ⟨i.byteIdx + 3⟩ != '-' then
    s.mkError "<!--"
  else
    -- Departure from spec: allow contents to begin with `>` or `->`.
    commentContentsFn c (s.setPos ⟨i.byteIdx + 4⟩)

/-- Parses an [HTML comment](https://html.spec.whatwg.org/dev/syntax.html#comments). -/
def comment : Parser where
  fn := nodeFn commentKind <| rawFn commentFn (trailingWs := false)

@[combinator_parenthesizer comment, parenthesizer Lean.Html.Syntax.comment]
def comment.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter comment, formatter Lean.Html.Syntax.comment]
def comment.formatter := Formatter.visitAtom commentKind

/-- Text contents of an HTML comment, excluding start and end markers. -/
def Comment.view [Monad m] [MonadError m] : Comment → m String
  | ⟨.node _ _ #[.atom _ s]⟩ => return s.drop 4 |>.dropEnd 3 |>.toString
  | _ => Elab.throwUnsupportedSyntax

/-! ## Tag names -/

abbrev tagNameKind := `Lean.Html.Syntax.tagName
abbrev TagName := TSyntax tagNameKind

/-- Parses an [HTML tag name](https://html.spec.whatwg.org/dev/syntax.html#syntax-tag-name):
an ASCII letter followed by characters other than ASCII whitespace, U+0000 NULL, `/`, `>`.
This includes [custom element names](https://html.spec.whatwg.org/dev/custom-elements.html#valid-custom-element-name). -/
@[run_parser_attribute_hooks]
def tagName : Parser :=
  parseFirstMany tagNameKind "tag name" Char.isAlpha isTagNameChar
where
  isTagNameChar (c : Char) : Bool :=
    !isAsciiWhitespace c && c.toNat != 0x0000 && c ∉ ['/', '>']

def TagName.view [Monad m] [MonadError m] : TagName → m String :=
  viewNodeAtom

/-! ## Attribute names -/

abbrev attrNameKind := `Lean.Html.Syntax.attrName
abbrev AttrName := TSyntax attrNameKind

/-- Parses an [HTML attribute name](https://html.spec.whatwg.org/dev/syntax.html#attributes-2)
that does not start with {lit}`{` (which would conflict with interpolation). -/
@[run_parser_attribute_hooks]
def attrName : Parser :=
  parseFirstMany attrNameKind "attribute name" isAttrNameFirstChar isAttrNameChar
where
  isAttrNameFirstChar (c : Char) : Bool := isAttrNameChar c && c != '{'
  /-- https://html.spec.whatwg.org/dev/syntax.html#attributes-2 -/
  isAttrNameChar (c : Char) : Bool :=
    !isControl c && c ∉ [' ', '"', '\'', '>', '/', '='] && !isNonCharacter c

def AttrName.view [Monad m] [MonadError m] : AttrName → m String :=
  viewNodeAtom

/-! ## Attribute values -/

abbrev attrValKind := `Lean.Html.Syntax.attrVal
abbrev AttrVal := TSyntax attrValKind

@[run_parser_attribute_hooks]
def attrVal : Parser :=
  node attrValKind (strLit <|> interp (trailingWs := true))

inductive AttrValView where
  /-- A string literal and its value {name}`val`, with character references decoded. -/
  | str (stx : TSyntax `str) (val : String)
  | interp (val : Term)
  deriving Inhabited

/-- Provides a view on the attribute value,
decoding character references when the value is a string literal.

Throws if an invalid character reference is encountered. -/
def AttrVal.view [Monad m] [MonadError m] (stx : AttrVal) : m AttrValView := do
  let c := stx.raw[0]
  if c.getKind == `str then
    return .str ⟨c⟩ (← decodeCharacterReferences ⟨c⟩)
  else if c.getKind == interpKind then
    return .interp ⟨c[1]⟩
  else
    Elab.throwUnsupportedSyntax

/-! ## Attributes -/

abbrev attrKind := `Lean.Html.Syntax.attr
abbrev Attr := TSyntax attrKind

/-- Parses an [HTML attribute](https://html.spec.whatwg.org/dev/syntax.html#attributes-2).
We support double-quoted attribute values {lit}`<tag name="val">`,
empty attributes {lit}`<tag name>`,
interpolations of one value {lit}`<tag name={ term }>`,
and interpolations of a sequence of attributes {lit}`<tag {... term }/>`.
Character references are decoded in double-quoted values. -/
@[run_parser_attribute_hooks]
def attr : Parser :=
  node attrKind <|
    (attrName >> optional (rawSymbol "=" (trailingWs := true) >> attrVal))
    -- `{...` should be tried before its prefix `{`.
    <|> interpMany (trailingWs := true) <|> interp (trailingWs := true)

inductive AttrView where
  | val (name : AttrName) (val : AttrVal)
  | bool (name : AttrName)
  | interp (val : Term)
  | interpMany (val : Term)
  deriving Inhabited

def Attr.view [Monad m] [MonadError m] (stx : Attr) : m AttrView :=
  let c := stx.raw[0]
  if c.getKind == attrNameKind then
    let val? := stx.raw[1]
    if val?.getNumArgs == 0 then
      return .bool ⟨c⟩
    else
      return .val ⟨c⟩ ⟨val?[1]⟩
  else if c.getKind == interpKind then
    return .interp ⟨c[1]⟩
  else if c.getKind == interpManyKind then
    return .interpMany ⟨c[1]⟩
  else
    Elab.throwUnsupportedSyntax

/-! ## Elements -/

abbrev elementKind := `Lean.Html.Syntax.element
abbrev Element := TSyntax elementKind

@[run_parser_attribute_hooks]
def elementWith (content : Parser) : Parser :=
  node elementKind <|
    rawSymbol "<" >> tagName >> many (ppSpace >> attr) >>
      (rawSymbol "/>" (expected := expected) <|>
        (rawSymbol ">" (expected := expected) >> content >>
          rawSymbol "</" >> tagName >> rawSymbol ">"))
where
  /-- Lists the possible contents of a tag. -/
  expected := ["attribute", "'/>'", "'>'"]

/-! ## Content

Content is not a syntax category because a category parser starts by reading a Lean token,
which fails on text that begins with whitespace or, for example, `'`.
Instead, {lit}`contentItemFn` dispatches to item parsers based on the next character. -/

abbrev contentKind := `Lean.Html.Syntax.content
/-- A sequence of HTML text nodes, comments, elements, and interpolations. -/
abbrev Content := TSyntax contentKind

def contentWith (itemFn : ParserFn) : Parser :=
  let antiquotP := mkAntiquot "content" contentKind
  let contentFn := nodeFn contentKind (manyAux itemFn)
  { -- Collects the tokens and node kinds of all items
    -- so that they are registered along with any syntax that uses `content`.
    info := orelseInfo antiquotP.info <| nodeInfo contentKind <| noFirstTokenInfo <|
      andthenInfo (elementWith skip).info <| andthenInfo interp.info <|
      andthenInfo comment.info text.info
    -- Antiquotations are only recognized inside quotations, so that `$` is text in literals.
    fn c s := if c.quotDepth > 0 then (withAntiquotFn antiquotP.fn contentFn) c s else contentFn c s
  }

private partial def contentItemFn : ParserFn := fun c s =>
  let i := s.pos
  match c.get i with
  | '<' =>
    match c.get ⟨i.byteIdx + 1⟩ with
    | '!' => comment.fn c s
    | '/' => s.mkError "HTML content"
    | _ => (elementWith (contentWith contentItemFn)).fn c s
  | '{' => interp.fn c s
  | _ => text.fn c s

/-- Parses a sequence of HTML content nodes:
{name}`text` contents, {name}`comment`s, {lit}`element`s, and {name}`interp`olations.

This parser can be antiquoted. -/
def content : Parser := contentWith contentItemFn

mutual
partial def content.parenthesizer : Parenthesizer :=
  Parenthesizer.withAntiquot.parenthesizer
      (Parenthesizer.mkAntiquot.parenthesizer' "content" contentKind) do
  Parenthesizer.checkKind contentKind
  let stx ← Syntax.MonadTraverser.getCur
  Parenthesizer.visitArgs <| stx.getArgs.size.forM fun _ _ => contentItem.parenthesizer

partial def contentItem.parenthesizer : Parenthesizer := do
  let k := (← Syntax.MonadTraverser.getCur).getKind
  if k == textKind then text.parenthesizer
  else if k == commentKind then comment.parenthesizer
  else if k == interpKind then interp.parenthesizer
  else if k == elementKind then elementWith.parenthesizer content.parenthesizer
  else throwError "Unexpected syntax node kind `{k}` in HTML content"
end

mutual
partial def content.formatter : Formatter :=
  Formatter.withAntiquot.formatter (Formatter.mkAntiquot.formatter' "content" contentKind) do
  Formatter.checkKind contentKind
  let stx ← Syntax.MonadTraverser.getCur
  Formatter.visitArgs <| stx.getArgs.size.forM fun _ _ => contentItem.formatter

partial def contentItem.formatter : Formatter := do
  let k := (← Syntax.MonadTraverser.getCur).getKind
  if k == textKind then text.formatter
  else if k == commentKind then comment.formatter
  else if k == interpKind then interp.formatter
  else if k == elementKind then elementWith.formatter content.formatter
  else throwError "Unexpected syntax node kind `{k}` in HTML content"
end

attribute [combinator_parenthesizer content, parenthesizer Lean.Html.Syntax.content]
  content.parenthesizer
attribute [combinator_formatter content, formatter Lean.Html.Syntax.content] content.formatter

/-- Parses an HTML element:
{lit}`<tag attr*/>` or {lit}`<tag attr*>content</tag>`.
Tags must be closed: void element syntax such as `<br>`,
and implied end tags such as `<ul><li>item</ul>`,
are not supported.

Start and end tag names are not checked for equality in the parser. -/
@[run_parser_attribute_hooks]
def element : Parser := elementWith (content)

inductive ContentItemView where
  | element (stx : Element) (startTag : TagName) (attrs : Array Attr) (children? : Option Content)
  /-- A run of text nodes and comments, together with its normalized text content
  (which may be empty). -/
  | text (stxs : Array (Text ⊕ Comment)) (content : String)
  | interp (v : Term)

/-- The syntax of this content node. Useful for reporting elaboration errors. -/
def ContentItemView.getSyntax : ContentItemView → Syntax
  | .element e .. => e.raw
  | .text ts _ => mkNullNode (ts.map (Sum.elim TSyntax.raw TSyntax.raw))
  | .interp v => v.raw

/-- Returns the sequence of items in an HTML {name}`content` node.

Runs of text interspersed with comments are merged and _normalized_:
- Consecutive whitespace is collapsed into a single space (U+0020),
  except at the start and end of {name}`c` — whitespace there is dropped.
- HTML character references are decoded into the Unicode characters they represent.

Throws if the end tag of any directly nested element does not match its start tag (up to casing),
or if an invalid character reference is encountered in text. -/
def Content.view (c : Content) : CoreM (Array ContentItemView) := do
  let mut items : Array ContentItemView := #[]
  -- Text/comment nodes since the last element or interpolation.
  let mut tcs : Array (Text ⊕ Comment) := #[]
  for stx in c.raw.getArgs do
    let k := stx.getKind
    if k == textKind then
      tcs := tcs.push <| .inl ⟨stx⟩
    else if k == commentKind then
      tcs := tcs.push <| .inr ⟨stx⟩
    else
      items ← pushText items tcs (trimEnd := false)
      tcs := #[]
      items := items.push (← viewItem stx)
  pushText items tcs (trimEnd := true)
where
  /-- Appends the normalized text of {name}`tcs` to {name}`items`. -/
  pushText (items : Array ContentItemView) (tcs : Array (Text ⊕ Comment)) (trimEnd : Bool) :
      CoreM (Array ContentItemView) := do
    -- Discard whitespace in the text/comment run that precedes all items.
    let trimStart := items.isEmpty
    let mut acc : TextAcc := {}
    for tc in tcs do
      let .inl t := tc | continue
      acc ← withRef t <| acc.push t (trimStart := trimStart)
    let val := acc.finish trimStart trimEnd
    return items.push (.text tcs val)
  viewItem (stx : Syntax) : CoreM ContentItemView := withRef stx do
    let k := stx.getKind
    if k == interpKind then
      return .interp ⟨stx[1]⟩
    else if k == elementKind then
      let startTag : TagName := ⟨stx[1]⟩
      let attrs : Array Attr := stx[2].getArgs.map (⟨·⟩)
      if stx.getNumArgs == 4 then
        return .element ⟨stx⟩ startTag attrs none
      let endTag : TagName := ⟨stx[6]⟩
      let startTagName ← TagName.view startTag
      let endTagName ← TagName.view endTag
      if endTagName.toLower != startTagName.toLower then
        let hint ← MessageData.hint m!"Replace with start tag" #[startTagName] (ref? := endTag)
        throwErrorAt endTag m!"Mismatched end tag, expected `{startTagName}` but got `{endTagName}`{hint}"
      return .element ⟨stx⟩ startTag attrs (some ⟨stx[4]⟩)
    else
      Elab.throwUnsupportedSyntax

end Lean.Html.Syntax
