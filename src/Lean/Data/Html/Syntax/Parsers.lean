/-
Copyright (c) 2023-2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen, Wojciech Nawrocki
-/
module

prelude
public import Lean.PrettyPrinter.Parenthesizer
public import Lean.PrettyPrinter.Formatter
import Lean.DocString.Parser

set_option doc.verso true

public section

namespace Lean.Html.Syntax

open Parser Doc.Parser PrettyPrinter

/-! # Code points -/

/-- Whether {name}`c` is a [control](https://infra.spec.whatwg.org/#control) code point. -/
def isControl (c : Char) : Bool :=
  let n := c.toNat
  n ≤ 0x001F || (n ≥ 0x007F && n ≤ 0x009F)

/-- Whether {name}`c` is [ASCII whitespace](https://infra.spec.whatwg.org/#ascii-whitespace).
Differs from {name}`Char.isWhitespace` by also including FF U+000C. -/
def isAsciiWhitespace (c : Char) : Bool :=
  c.toNat ∈ [0x0009, 0x000A, 0x000C, 0x000D, 0x0020]

/-- Whether {name}`c` is a [noncharacter](https://infra.spec.whatwg.org/#noncharacter). -/
def isNonCharacter (c : Char) : Bool :=
  let n := c.toNat
  (n ≥ 0xFDD0 && n ≤ 0xFDEF) ||
  n ∈ [0xFFFE, 0xFFFF, 0x1FFFE, 0x1FFFF, 0x2FFFE, 0x2FFFF, 0x3FFFE, 0x3FFFF, 0x4FFFE,
    0x4FFFF, 0x5FFFE, 0x5FFFF, 0x6FFFE, 0x6FFFF, 0x7FFFE, 0x7FFFF, 0x8FFFE, 0x8FFFF,
    0x9FFFE, 0x9FFFF, 0xAFFFE, 0xAFFFF, 0xBFFFE, 0xBFFFF, 0xCFFFE, 0xCFFFF, 0xDFFFE,
    0xDFFFF, 0xEFFFE, 0xEFFFF, 0xFFFFE, 0xFFFFF, 0x10FFFE, 0x10FFFF]


/-! # Helpers -/

/-- Parses one character matching {name}`firstP` followed by many matching {name}`manyP`,
followed by whitespace (which is not stored).
The result is stored in an atom wrapped in a node of the given {name}`kind`. -/
private def parseFirstMany (kind : Name) (firstP manyP : Char → Bool) : Parser where
  fn := andthenFn parse (takeWhileFn Char.isWhitespace)
where
  parse :=
    atomicFn <|
      nodeFn kind <|
        asStringFn <| andthenFn (satisfyFn firstP) (manyFn (satisfyFn manyP))

private def viewNodeAtom [Monad m] [MonadError m] : TSyntax k → m String
  | ⟨.node _ _ #[.atom _ s]⟩ => return s
  | _ => Elab.throwUnsupportedSyntax

/-! # Tag names -/

abbrev tagNameKind := `Lean.Html.Syntax.tagName
abbrev TagName := TSyntax tagNameKind

def TagName.view [Monad m] [MonadError m] : TagName → m String :=
  viewNodeAtom

private def tagNameNoAntiquot : Parser :=
  parseFirstMany tagNameKind Char.isAlpha isTagNameChar
where
  isTagNameChar (c : Char) : Bool :=
    !isAsciiWhitespace c && c.toNat != 0x0000 && c ∉ ['/', '>']

/-- Parses an [HTML tag name](https://html.spec.whatwg.org/dev/syntax.html#syntax-tag-name):
an ASCII letter followed by characters other than ASCII whitespace, U+0000 NULL, `/`, `>`.
This includes [custom element names](https://html.spec.whatwg.org/dev/custom-elements.html#valid-custom-element-name). -/
def tagName : Parser :=
  withAntiquot (mkAntiquot "tagName" tagNameKind) tagNameNoAntiquot

@[combinator_parenthesizer tagName]
def tagName.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter tagName]
def tagName.formatter := Formatter.visitAtom tagNameKind

/-! # Attribute names -/

abbrev attrNameKind := `Lean.Html.Syntax.attrName
abbrev AttrName := TSyntax attrNameKind

def AttrName.view [Monad m] [MonadError m] : AttrName → m String :=
  viewNodeAtom

private def attrNameNoAntiquot : Parser :=
  parseFirstMany attrNameKind isAttrNameFirstChar isAttrNameChar
where
  /-- Divergence from the spec: attribute names can't start with `{`, `}`, `<`, or `$`.
  The spec allows these characters, but they make parser errors worse
  (and `$` conflicts with antiquotations). -/
  isAttrNameFirstChar (c : Char) : Bool := isAttrNameChar c && c ∉ ['{', '}', '<', '$']
  /-- https://html.spec.whatwg.org/dev/syntax.html#attributes-2 -/
  isAttrNameChar (c : Char) : Bool :=
    !isControl c && c ∉ [' ', '"', '\'', '>', '/', '='] && !isNonCharacter c

/-- Parses an [HTML attribute name](https://html.spec.whatwg.org/dev/syntax.html#attributes-2)
that does not start with any of `{`, `}`, `<`, `$`. -/
def attrName : Parser :=
  withAntiquot (mkAntiquot "attrName" attrNameKind) attrNameNoAntiquot

@[combinator_parenthesizer attrName]
def attrName.parenthesizer := Parenthesizer.visitToken

@[combinator_formatter attrName]
def attrName.formatter := Formatter.visitAtom attrNameKind

/-! # Text content -/

abbrev textKind := `Lean.Html.Syntax.text
abbrev Text := TSyntax textKind

/-- Returns the source text of an HTML text node,
including any trailing whitespace and with character references not yet decoded. -/
def Text.view [Monad m] [MonadError m] : Text → m String :=
  viewNodeAtom

private def textNoAntiquot : Parser where
  fn c s :=
    let startPos := s.pos
    let s := takeWhile1Fn isTextChar "expected HTML text" c s
    mkNodeToken textKind startPos true c s
where
  isTextChar (c : Char) :=
    (!isControl c || isAsciiWhitespace c) && !isNonCharacter c && c ∉ ['{', '}', '<', '>']

/-- Parses [HTML text content](https://html.spec.whatwg.org/dev/dom.html#text-content)
that does not contain interpolation markers (`{`, `}`) or angle brackets (`<`, `>`). -/
def text : Parser :=
  /- This is almost `withAntiquot (mkAntiquot "text" textKind) textNoAntiquot`,
  but `acceptLhs` is used to ensure that `$t:text` is parsed as the antiquotation
  rather than as text content when the latter would yield a longer parse. -/
  let antiquotP := mkAntiquot "text" textKind
  { fn c s :=
      if c.get s.pos == '$' then
        orelseFnCore (antiquotBehavior := .acceptLhs) antiquotP.fn textNoAntiquot.fn c s
      else
        textNoAntiquot.fn c s
    info := orelseInfo antiquotP.info textNoAntiquot.info }

@[combinator_formatter text]
def text.formatter : Formatter := Formatter.visitAtom textKind

@[combinator_parenthesizer text]
def text.parenthesizer : Parenthesizer := Parenthesizer.visitToken

end Lean.Html.Syntax
