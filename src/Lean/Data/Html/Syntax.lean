/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Wojciech Nawrocki
-/
module

prelude
import Init.Data.String.Modify
public import Lean.PrettyPrinter.Parenthesizer
public import Lean.PrettyPrinter.Formatter
import Lean.DocString.Parser
import Lean.Meta.Hint
import Lean.Data.Html.Spec

set_option doc.verso true

public section

namespace Lean.Html.Syntax

open Parser Doc.Parser PrettyPrinter

/-! # Parsers for HTML syntax

- Compliant with the [HTML living standard](https://html.spec.whatwg.org/dev/syntax.html#syntax)
  to the extent that it makes sense.
  Departures are documented on the appropriate parsers.
- HTML text, tags, and comment contents may contain reserved tokens such as `'`,
  and certain parsers (e.g. end tag `>` symbols) should not consume trailing whitespace,
  so that this whitespace is instead included in text content following those parsers.
  For these reasons we eschew Lean's standard mechanism of syntactic categories
  and dispatching to parsers based on the leading token
  in favor of hand-rolled parsers, formatters, etc.
  - All whitespace is preserved initially, and then collapsed in {lit}`Content.view`.
- To simplify away special handling of `$`, most parsers here cannot be antiquoted.
  Parsers that *can* be antiquoted are documented to support this.
-/

/-! ## Helpers -/

/-- Parses one character matching {name}`firstP` followed by many matching {name}`manyP`,
followed by whitespace (which is not stored).
The result is stored in an atom wrapped in a node of the given {name}`kind`.
{name}`expected` describes the expected input in error messages. -/
private def parseFirstMany (kind : Name) (expected : String) (firstP manyP : Char → Bool) :
    Parser where
  fn := andthenFn parse (takeWhileFn Char.isWhitespace)
where
  parse :=
    nodeFn kind <|
      asStringFn <| andthenFn first (manyFn (satisfyFn manyP))
  first : ParserFn := fun c s =>
    let i := s.pos
    if h : c.atEnd i then
      s.mkEOIError [expected]
    else if firstP (c.get' i h) then
      s.next' c i h
    else
      s.mkUnexpectedError s!"unexpected character '{c.get' i h}'" [expected]

@[combinator_parenthesizer parseFirstMany]
private def parseFirstMany.parenthesizer (_ : Name) (_ : String) (_ _ : Char → Bool) :=
  Parenthesizer.visitToken

@[combinator_formatter parseFirstMany]
private def parseFirstMany.formatter (kind : Name) (_ : String) (_ _ : Char → Bool) :=
  Formatter.visitAtom kind

private def viewNodeAtom [Monad m] [MonadError m] : TSyntax k → m String
  | ⟨.node _ _ #[.atom _ s]⟩ => return s
  | _ => Elab.throwUnsupportedSyntax

/-! ## Raw symbols -/

private def rawSymbolFn (sym : String) : ParserFn :=
  let expected := s!"'{sym}'"
  rawFn fun c s =>
    let i := s.pos
    let j : String.Pos.Raw := ⟨i.byteIdx + sym.utf8ByteSize⟩
    if j.byteIdx ≤ c.endPos.byteIdx && c.extract i j == sym then
      s.setPos j
    else if c.atEnd i then
      s.mkEOIError [expected]
    else
      let s := tokenFn [expected] c s
      if s.hasError then s else s.mkUnexpectedTokenErrors [expected] i

/-- Parses {name}`sym` as an atom.

Unlike {name}`symbol`, this parser does not consume trailing whitespace.
We rely on this to make whitespace in front of a symbol available to the next parser.

This parser also does not consult the token table, and {name}`sym` is not registered as a token. -/
def rawSymbol (sym : String) : Parser where
  fn := rawSymbolFn sym

@[combinator_parenthesizer rawSymbol]
def rawSymbol.parenthesizer (sym : String) := Parenthesizer.symbolNoAntiquot.parenthesizer sym

@[combinator_formatter rawSymbol]
def rawSymbol.formatter (sym : String) : Formatter := do
  -- No space is inserted after the symbol.
  Formatter.resetLeadWord
  Formatter.symbolNoAntiquot.formatter sym

/-! ## Interpolations -/

/-- Parses an interpolation: a Lean term between {name}`openSym` and {lit}`}`. -/
@[run_parser_attribute_hooks]
def interpWith (kind : SyntaxNodeKind) (openSym : String) : Parser :=
  /- The opening must be parsed as `symbol` rather than `rawSymbol`
  since `term` cannot handle leading whitespace. -/
  node kind (symbol openSym >> termParser >> rawSymbol "}")

abbrev interpKind := `Lean.Html.Syntax.interp
abbrev interpManyKind := `Lean.Html.Syntax.interpMany

/-- Parses {lit}`{ term }`. -/
def interp : Parser := interpWith interpKind "{"

/-- Parses {lit}`{... term }`. -/
def interpMany : Parser := interpWith interpManyKind "{..."

/-! ## Text content -/

abbrev textKind := `Lean.Html.Syntax.text
abbrev Text := TSyntax textKind

/-- Parses [HTML text content](https://html.spec.whatwg.org/dev/dom.html#text-content),
stopping at an interpolation `{`, a tag `<`, or a closing bracket `}` (for {lit}`html%{ text }`). -/
def text : Parser where
  fn c s :=
    let startPos := s.pos
    let s := takeWhile1Fn isTextChar "expected HTML text" c s
    mkNodeToken textKind startPos (includeWhitespace := false) c s
where
  isTextChar (c : Char) :=
    (!isControl c || isAsciiWhitespace c) && !isNonCharacter c && c ∉ ['{', '}', '<']

@[combinator_parenthesizer text]
def text.parenthesizer : Parenthesizer := Parenthesizer.visitToken

@[combinator_formatter text]
def text.formatter : Formatter := Formatter.visitAtom textKind

/-- Returns the raw source text of an HTML text node,
with whitespace not yet normalized and character references not yet decoded. -/
def Text.view [Monad m] [MonadError m] : Text → m String :=
  viewNodeAtom

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

@[combinator_parenthesizer comment]
def comment.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter comment]
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
that does not start with `{` (which would conflict with interpolation). -/
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

def attrVal : Parser :=
  node attrValKind (strLit <|> interp)

@[combinator_parenthesizer attrVal]
def attrVal.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter attrVal]
def attrVal.formatter := Formatter.visitAtom attrValKind

inductive AttrValView where
  | str (val : TSyntax `str)
  | interp (val : Term)
  deriving Inhabited

def AttrVal.view [Monad m] [MonadError m] (stx : AttrVal) : m AttrValView :=
  let c := stx.raw[0]
  if c.getKind == `str then
    return .str ⟨c⟩
  else if c.getKind == interpKind then
    return .interp ⟨c⟩
  else
    Elab.throwUnsupportedSyntax

/-! ## Attributes -/

abbrev attrKind := `Lean.Html.Syntax.attr
abbrev Attr := TSyntax attrKind

/-- Parses an [HTML attribute](https://html.spec.whatwg.org/dev/syntax.html#attributes-2).
We support double-quoted attribute values {lit}`<tag name="val">`,
empty attributes {lit}`<tag name>`,
interpolations of one value {lit}`<tag name={ term }>`,
and interpolations of a sequence of attributes {lit}`<tag {... term }/>`. -/
def attr : Parser :=
  node attrKind <|
    (attrName >> symbol "=" >> attrVal) <|> attrName <|> interp <|> interpMany

@[combinator_parenthesizer attr]
def attr.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter attr]
def attr.formatter := Formatter.visitAtom attrKind

inductive AttrView where
  | val (name : AttrName) (val : AttrVal)
  | bool (name : AttrName)
  | interp (val : Term)
  | interpMany (val : Term)
  deriving Inhabited

def Attr.view [Monad m] [MonadError m] (stx : Attr) : m AttrView :=
  let c := stx.raw[0]
  if c[0].getKind == attrNameKind && c[2].getKind == attrValKind then
    return .val ⟨c[0]⟩ ⟨c[2]⟩
  else if c.getKind == attrNameKind then
    return .bool ⟨c⟩
  else if c.getKind == interpKind then
    return .interp ⟨c⟩
  else if c.getKind == interpManyKind then
    return .interpMany ⟨c⟩
  else
    Elab.throwUnsupportedSyntax

/-! ## Elements -/

abbrev elementKind := `Lean.Html.Syntax.element
abbrev Element := TSyntax elementKind

@[run_parser_attribute_hooks]
def elementWith (content : Parser) : Parser :=
  node elementKind <|
    rawSymbol "<" >> tagName >> many (ppSpace >> attr) >>
      (rawSymbol "/>" <|> (rawSymbol ">" >> content >> rawSymbol "</" >> tagName >> rawSymbol ">"))

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

/-- Parses an HTML element:
{lit}`<tag attr*/>` or {lit}`<tag attr*>content</tag>`.
Tags must be closed: void element syntax such as `<br>`,
and implied end tags such as `<ul><li>item</ul>`,
are not supported.

Start and end tag names are not checked for equality in the parser. -/
def element : Parser := elementWith (contentWith contentItemFn)

/-- Parses a sequence of HTML content nodes:
{name}`text` contents, {name}`comment`s, {name}`element`s, and {name}`interp`olations.

This parser can be antiquoted. -/
def content : Parser := contentWith contentItemFn

mutual
@[combinator_parenthesizer content]
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
  else if k == interpKind then interpWith.parenthesizer interpKind "{"
  else if k == elementKind then elementWith.parenthesizer content.parenthesizer
  else throwError "Unexpected syntax node kind `{k}` in HTML content"
end

mutual
@[combinator_formatter content]
partial def content.formatter : Formatter :=
  Formatter.withAntiquot.formatter (Formatter.mkAntiquot.formatter' "content" contentKind) do
  Formatter.checkKind contentKind
  let stx ← Syntax.MonadTraverser.getCur
  Formatter.visitArgs <| stx.getArgs.size.forM fun _ _ => contentItem.formatter

partial def contentItem.formatter : Formatter := do
  let k := (← Syntax.MonadTraverser.getCur).getKind
  if k == textKind then text.formatter
  else if k == commentKind then comment.formatter
  else if k == interpKind then interpWith.formatter interpKind "{"
  else if k == elementKind then elementWith.formatter content.formatter
  else throwError "Unexpected syntax node kind `{k}` in HTML content"
end

inductive ContentItemView where
  | element (stx : Element) (startTag : TagName) (attrs : Array Attr) (children? : Option Content)
  | text (t : Text)
  | interp (v : Term)
  | comment (c : Comment)

/-- The syntax of this content node. Useful for reporting elaboration errors. -/
def ContentItemView.getSyntax : ContentItemView → Syntax
  | .element e .. => e.raw
  | .text t => t.raw
  | .interp v => v.raw
  | .comment c => c.raw

/-- Returns the sequence of items in an HTML {name}`content` node.
Throws if the end tag of any directly nested element does not match its start tag. -/
def Content.view (c : Content) : CoreM (Array ContentItemView) :=
  c.raw.getArgs.mapM viewItem
where
  viewItem (stx : Syntax) : CoreM ContentItemView := withRef stx do
    let k := stx.getKind
    if k == textKind then
      return .text ⟨stx⟩
    else if k == commentKind then
      return .comment ⟨stx⟩
    else if k == interpKind then
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
