/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Parser.Basic
namespace Lean.Parser

def isQuotableCharForStrInterpolant (c : Char) : Bool :=
  c == '{' || isQuotableCharDefault c

partial def interpolatedStrFn (p : ParserFn) : ParserFn := fun c s =>
  let input     := c.input
  let stackSize := s.stackSize
  let rec parse (startPos : String.Pos) (c : ParserContext) (s : ParserState) : ParserState :=
    let i     := s.pos
    if input.atEnd i then
      let s := s.mkError "unterminated string literal"
      s.mkNode interpolatedStrKind stackSize
    else
      let curr := input.get i
      let s    := s.setPos (input.next i)
      if curr == '\"' then
        let s := mkNodeToken interpolatedStrLitKind startPos c s
        s.mkNode interpolatedStrKind stackSize
      else if curr == '\\' then
        andthenFn (quotedCharCoreFn isQuotableCharForStrInterpolant true) (parse startPos) c s
      else if curr == '{' then
        let s := mkNodeToken interpolatedStrLitKind startPos c s
        let s := p c s
        if s.hasError then s
        else
          let i := s.pos
          let curr := input.get i
          if curr == '}' then
            let s := s.setPos (input.next i)
            parse i c s
          else
            let s := s.mkError "'}'"
            s.mkNode interpolatedStrKind stackSize
      else
        parse startPos c s
  let startPos := s.pos
  if input.atEnd startPos then
    s.mkEOIError
  else
    let curr  := input.get s.pos;
    if curr != '\"' then
      s.mkError "interpolated string"
    else
      let s := s.next input startPos
      parse startPos c s

@[inline] def interpolatedStrNoAntiquot (p : Parser) : Parser := {
  fn   := interpolatedStrFn (withoutPosition p).fn,
  info := mkAtomicInfo "interpolatedStr"
}

/-- The parser `interpolatedStr(p)` parses a string literal like `"foo"` (see `str`), but the string
may also contain `{}` escapes, and within the escapes the parser `p` is used. For example,
`interpolatedStr(term)` will parse `"foo {2 + 2}"`, where `2 + 2` is parsed as a term rather than
as a string. Note that the full Lean term grammar is available here, including string literals,
so for example `"foo {"bar" ++ "baz"}"` is a legal interpolated string (which evaluates to
`foo barbaz`).

This parser has arity 1, and returns a `interpolatedStrKind` with an odd number of arguments,
alternating between chunks of literal text and results from `p`. The literal chunks contain
uninterpreted substrings of the input. For example, `"foo\n{2 + 2}"` would have three arguments:
an atom `"foo\n{`, the parsed `2 + 2` term, and then the atom `}"`. -/
def interpolatedStr (p : Parser) : Parser :=
  withAntiquot (mkAntiquot "interpolatedStr" interpolatedStrKind) $ interpolatedStrNoAntiquot p

end Lean.Parser
