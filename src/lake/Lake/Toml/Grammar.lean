/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Toml.ParserUtil

/-!
# TOML Grammar

A Lean encoding of the v1.0.0 TOML grammar ([en][1], [abnf]][2])
using `Lean.Parser` objects. The current encoding elides the use of
tokens entirely, relying purely on custom parser functions.

[1]: https://toml.io/en/v1.0.0
[2]: https://github.com/toml-lang/toml/blob/1.0.0/toml.abnf
-/

namespace Lake.Toml

open Lean Parser

--------------------------------------------------------------------------------
/-! ## Trailing Functions -/
--------------------------------------------------------------------------------

/-- Consume optional horizontal whitespace (i.e., tab or space). -/
def wsFn : ParserFn :=
  takeWhileFn fun c => c = ' ' || c = '\t'

/-- Consumes the LF following a CR in a CRLF newline. -/
def crlfAuxFn : ParserFn := fun c s =>
  let input := c.input
  let errMsg := "invalid newline; no LF after CR"
  if h : input.atEnd s.pos then
    s.mkUnexpectedError errMsg
  else
    let curr := input.get' s.pos h
    if curr == '\n' then
      s.next' input s.pos h
    else
      s.mkUnexpectedError errMsg

/-- Consume a newline. -/
def newlineFn : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkEOIError ["newline"]
  else
    let curr := input.get' s.pos h
    if curr == '\n' then
      s.next' input s.pos h
    else if curr == '\r' then
      crlfAuxFn c (s.next' input s.pos h)
    else
      mkUnexpectedCharError s curr ["newline"]

/-- Consumes the body of a comment. -/
def commentBodyFn : ParserFn :=
  takeWhileFn fun c => c.val ≥ 0x20 || c == '\t'

/-- Consumes a line comment. -/
def commentFn : ParserFn :=
  chFn '#' ["comment"] >> commentBodyFn

/-- Consume optional whitespace (space, tab, or newline). -/
partial def wsNewlineFn : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s
  else
    let curr := input.get' s.pos h
    if curr = ' ' || curr = '\t' || curr == '\n' then
      wsNewlineFn c (s.next' input s.pos  h)
    else if curr == '\r' then
      (crlfAuxFn >> wsNewlineFn) c (s.next' input s.pos  h)
    else
      s

/-- Consume optional sequence of whitespace / newline(s) / comment (s). -/
partial def trailingFn : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s
  else
    let curr := input.get' s.pos h
    if curr = ' ' || curr = '\t' || curr == '\n' then
      trailingFn c (s.next' input s.pos h)
    else if curr == '\r' then
      (crlfAuxFn >> trailingFn) c (s.next' input s.pos h)
    else if curr == '#' then
      (commentBodyFn >> trailingFn) c (s.next' input s.pos h)
    else
      s

--------------------------------------------------------------------------------
/-! ## Strings -/
--------------------------------------------------------------------------------

/-- A TOML character escape. -/
def isEscapeChar (c : Char) : Bool :=
  c == 'b' || c == 't' || c == 'n' || c == 'f' || c == 'r' || c == '\"' || c == '\\'

/-- Consumes a TOML string escape sequence after a `\`. -/
def escapeSeqFn (stringGap : Bool) : ParserFn := fun c s =>
  let input := c.input
  let expected := ["escape sequence"]
  if h : input.atEnd s.pos then
    s.mkEOIError expected
  else
    let curr := input.get' s.pos h
    if isEscapeChar curr then
      s.next' input s.pos h
    else if curr == 'u' then
      repeatFn 4 hexDigitFn c (s.next' input s.pos h)
    else if curr == 'U' then
      repeatFn 8 hexDigitFn c (s.next' input s.pos h)
    else if curr == ' ' || curr == '\t' || curr == '\n' then
      let s := s.next' input s.pos h
      if stringGap then
        wsNewlineFn c s
      else
        s.mkUnexpectedError "string gap is forbidden here" expected
    else if curr == '\r' then
      let s := s.next' input s.pos h
      if stringGap then
        (crlfAuxFn >> wsNewlineFn) c s
      else
        s.mkUnexpectedError "string gap is forbidden here" expected
    else
      s.mkUnexpectedError "invalid escape sequence"

partial def basicStringAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkUnexpectedErrorAt "unterminated basic string" startPos
  else
    let curr := input.get' s.pos h
    let s := s.next' input s.pos h
    if curr == '\"' then
      s
    else if curr == '\\' then
      (escapeSeqFn false >> basicStringAuxFn startPos) c s
    else
      basicStringAuxFn startPos c s

def basicStringFn : ParserFn := usePosFn fun startPos =>
  chFn '\"' ["basic string"] >> basicStringAuxFn startPos

partial def literalStringAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkUnexpectedErrorAt "unterminated literal string" startPos
  else
    let curr := input.get' s.pos h
    let s := s.next' input s.pos h
    if curr == '\'' then
      s
    else
      literalStringAuxFn startPos c s

def literalStringFn : ParserFn := usePosFn fun startPos =>
  chFn '\'' ["literal string"] >> literalStringAuxFn startPos

partial def mlLiteralStringAuxFn (startPos : String.Pos) (quoteDepth : Nat)  : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    if quoteDepth ≥ 3 then
      s
    else
      s.mkUnexpectedErrorAt "unterminated multi-line literal string" startPos
  else
    let curr := input.get' s.pos h
    if curr == '\'' then
      let s := s.next' input s.pos h
      if quoteDepth ≥ 5 then
        s.mkUnexpectedError "too many quotes"
      else
        mlLiteralStringAuxFn startPos (quoteDepth+1) c s
    else if quoteDepth ≥ 3 then
      s
    else
      let s := s.next' input s.pos h
      mlLiteralStringAuxFn startPos 0 c s

def mlLiteralStringFn : ParserFn := usePosFn fun startPos =>
  atomicFn (repeatFn 3 (chFn '\'' ["multi-line literal string"])) >>
  mlLiteralStringAuxFn startPos 0

partial def mlBasicStringAuxFn (startPos : String.Pos) (quoteDepth : Nat)  : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    if quoteDepth ≥ 3 then
      s
    else
      s.mkUnexpectedErrorAt "unterminated multi-line basic string" startPos
  else
    let curr := input.get' s.pos h
    if curr == '\"' then
      let s := s.next' input s.pos h
      if quoteDepth ≥ 5 then
        s.mkUnexpectedError "too many quotes"
      else
        mlBasicStringAuxFn startPos (quoteDepth+1) c s
    else if quoteDepth ≥ 3 then
      s
    else if curr == '\\' then
      let s := s.next' input s.pos h
      (escapeSeqFn true >> mlBasicStringAuxFn startPos 0) c s
    else
      let s := s.next' input s.pos h
      mlBasicStringAuxFn startPos 0 c s

def mlBasicStringFn : ParserFn := usePosFn fun startPos =>
  atomicFn (repeatFn 3 (chFn '\"' ["multi-line basic string"])) >>
  mlBasicStringAuxFn startPos 0

--------------------------------------------------------------------------------
/-! ## Numerals (Date-Times, Floats, and Integers) -/
--------------------------------------------------------------------------------

def hourMinFn : ParserFn :=
  digitPairFn ["hour digit"] >> chFn ':' >> digitPairFn ["minute digit"]

def timeTailFn (allowOffset : Bool) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s
  else
    let curr := input.get' s.pos h
    if curr = '.' then
      let s := s.next' input s.pos h
      let s := takeWhile1Fn (·.isDigit) ["millisecond"] c s
      if s.hasError then s else
      if h : input.atEnd s.pos then s else
      timeOffsetFn (input.get' s.pos h) (input.next' s.pos h) c s
    else
      timeOffsetFn curr (input.next' s.pos h) c s
where
  @[inline] timeOffsetFn curr nextPos c s :=
    if curr == 'Z' || curr == 'z' then
      if allowOffset then s.setPos nextPos else
      s.mkUnexpectedError "time offset is forbidden here"
    else if curr = '+' || curr = '-' then
      if allowOffset then hourMinFn c (s.setPos nextPos) else
      s.mkUnexpectedError "time offset is forbidden here"
    else
      s

def timeAuxFn (allowOffset : Bool) : ParserFn :=
  digitPairFn ["minute digit"] >> chFn ':' >>
  digitPairFn ["second digit"] >> timeTailFn allowOffset

def timeFn (allowOffset := false) : ParserFn :=
  digitPairFn ["hour"] >> chFn ':' >> timeAuxFn allowOffset

def timeLitFn : ParserFn :=
  litFn `Lake.Toml.time timeFn

def optTimeFn : ParserFn := fun c s =>
  let i := s.pos
  let input := c.input
  if h : input.atEnd i then
    s
  else
    let curr := input.get' i h
    if curr = 'T' || curr = 't' || curr = ' ' then
      timeFn true c (s.next' input i h)
    else
      s

def dateTimeAuxFn : ParserFn :=
  digitPairFn ["month digit"] >> chFn '-' >>
  digitPairFn ["day digit"] >> optTimeFn

def dateTimeFn : ParserFn :=
  repeatFn 4 (digitFn ["year digit"]) >> chFn '-' >> dateTimeAuxFn

def dateTimeLitFn : ParserFn :=
  litFn `Lake.Toml.dateTime dateTimeFn

def decExpFn : ParserFn := fun c s =>
  let input := c.input
  let expected := ["decimal exponent"]
  if h : input.atEnd s.pos then
    s.mkEOIError expected
  else
    let curr := input.get' s.pos h
    if curr = '-' || curr == '+' then
      let s := s.next' input s.pos h
      sepByChar1Fn (·.isDigit) '_' expected c s
    else if curr.isDigit then
      let s := s.next' input s.pos h
      sepByChar1AuxFn (·.isDigit) '_' expected c s
    else
      mkUnexpectedCharError s curr expected

def optDecExpFn : ParserFn :=  fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s
  else
    let curr := input.get' s.pos h
    if curr == 'e' || curr == 'E' then
      decExpFn c (s.next' input s.pos h)
    else
      s

mutual

partial def decNumberSepFn (startPos : String.Pos) (curr : Char) (nextPos : String.Pos) : ParserFn := fun c s =>
  if curr == '_' then
    let s := s.setPos nextPos
    decNumberFn startPos c s
  else if curr == '.' then
    let s := s.setPos nextPos
    let s := sepByChar1Fn (·.isDigit) '_' ["decimal fraction"] c s
    if s.hasError then s else
    let s := optDecExpFn c s
    if s.hasError then s else
    pushLit `Lake.Toml.float startPos skipFn c s
  else if curr == 'e' || curr == 'E' then
    let s := s.setPos nextPos
    let s := decExpFn c s
    if s.hasError then s else
    pushLit `Lake.Toml.float startPos skipFn c s
  else
    pushLit `Lake.Toml.decInt startPos skipFn c s

partial def decNumberAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    pushLit `Lake.Toml.decInt startPos skipFn c s
  else
    let curr := input.get' s.pos h
    if curr.isDigit then
      let s := s.next' input s.pos h
      decNumberAuxFn startPos c s
    else
      decNumberSepFn startPos curr (input.next' s.pos h) c s

partial def decNumberFn (startPos : String.Pos) : ParserFn := fun c s =>
  let i := s.pos
  let input := c.input
  let expected := ["decimal integer", "float"]
  if h : input.atEnd i then
    s.mkEOIError expected
  else
    let curr := input.get' i h
    if curr.isDigit then
      let s := s.next' input i h
      decNumberAuxFn startPos c s
    else
      mkUnexpectedCharError s curr expected

end

def infAuxFn (startPos : String.Pos) : ParserFn :=
  strFn "nf" ["'inf'"] >> pushLit `Lake.Toml.float startPos

def nanAuxFn (startPos : String.Pos) : ParserFn :=
  strFn "an" ["'nan'"] >> pushLit `Lake.Toml.float startPos

def decimalFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  let expected := ["decimal integer", "float"]
  if h : input.atEnd s.pos then
    s.mkEOIError expected
  else
    let curr := input.get' s.pos h
    if curr.isDigit then
      decNumberAuxFn startPos c (s.next' input s.pos h)
    else if curr == 'i' then
      infAuxFn startPos c (s.next' input s.pos h)
    else if curr == 'n' then
      nanAuxFn startPos c (s.next' input s.pos h)
    else
      mkUnexpectedCharError s curr expected

def decNumeralAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkEOIError ["decimal integer", "float", "date-time"]
  else -- `NN`
    let curr := input.get' s.pos h
    let nextPos := input.next' s.pos h
    if curr.isDigit then
      let s := s.setPos nextPos
      if h : input.atEnd s.pos then
        pushLit `Lake.Toml.decInt startPos skipFn c s
      else
        let curr := input.get' s.pos h
        let nextPos := input.next' s.pos h
        if curr == ':' then -- `HH:`
          let s := s.setPos nextPos
          let s := timeAuxFn false c s
          if s.hasError then s else
          pushLit `Lake.Toml.time startPos skipFn c s
        else if curr.isDigit then -- `NNN`
          let s := s.setPos nextPos
          if h : input.atEnd s.pos then
            pushLit `Lake.Toml.decInt startPos skipFn c s
          else
            let curr := input.get' s.pos h
            let nextPos := input.next' s.pos h
            if curr.isDigit then -- `NNNN`
              let s := s.setPos nextPos
              if h : input.atEnd nextPos then
                pushLit `Lake.Toml.decInt startPos skipFn c s
              else
                let curr := input.get' s.pos h
                let nextPos := input.next' s.pos h
                if curr == '-' then -- `YYYY-`
                  let s := s.setPos nextPos
                  let s := dateTimeAuxFn c s
                  if s.hasError then s else
                  pushLit `Lake.Toml.dateTime startPos skipFn c s
                else if curr.isDigit then
                  let s := s.setPos nextPos
                  decNumberAuxFn startPos c s
                else
                  decNumberSepFn startPos curr nextPos c s
            else
              decNumberSepFn startPos curr nextPos c s
        else
          decNumberSepFn startPos curr nextPos c s
    else
      decNumberSepFn startPos curr nextPos c s

def numeralFn : ParserFn := fun c s =>
  let input := c.input
  let startPos := s.pos
  let expected := ["integer", "float", "date-time"]
  if h : input.atEnd s.pos then
    s.mkEOIError expected
  else
    let curr := input.get' s.pos h
    if curr == '0' then
      let s := s.next' input startPos h
      if h : input.atEnd s.pos then
        pushLit `Lake.Toml.decInt startPos skipFn c s
      else
        let curr := input.get' s.pos h
        if curr == 'b' then
          let s := s.next' input s.pos h
          let s := sepByChar1Fn isBinDigit '_' ["binary integer"] c s
          if s.hasError then s else
          pushLit `Lake.Toml.binInt startPos skipFn c s
        else if curr == 'o' then
          let s := s.next' input s.pos h
          let s := sepByChar1Fn isOctDigit '_' ["octal integer"] c s
          if s.hasError then s else
          pushLit `Lake.Toml.octInt startPos skipFn c s
        else if curr == 'x' then
          let s := s.next' input s.pos h
          let s := sepByChar1Fn isHexDigit '_' ["hexadecimal integer"] c s
          if s.hasError then s else
          pushLit `Lake.Toml.hexInt startPos skipFn c s
        else if curr.isDigit then
          let s := s.next' input s.pos h
          let s := (chFn ':' >> timeAuxFn false) c s
          if s.hasError then s else
          pushLit `Lake.Toml.time startPos skipFn c s
        else
          decNumberSepFn startPos curr (input.next' s.pos h) c s
    else if curr.isDigit then
      decNumeralAuxFn startPos c (s.next' input s.pos h)
    else if curr == '+' || curr == '-' then
      decimalFn startPos c (s.next' input s.pos h)
    else if curr == 'i' then
      infAuxFn startPos c (s.next' input s.pos h)
    else if curr == 'n' then
      nanAuxFn startPos c (s.next' input s.pos h)
    else
      s.mkUnexpectedError s!"unexpected '{curr}'" expected

--------------------------------------------------------------------------------
/-! ## Parsers -/
--------------------------------------------------------------------------------

def trailingWs : Parser :=
  trailing wsFn

def trailingSep : Parser :=
  trailing trailingFn

def unquotedKeyFn : ParserFn :=
  takeWhile1Fn (fun c => c.isAlphanum || c == '_' || c == '-') ["unquoted key"]

def unquotedKey : Parser :=
  litWithAntiquot "unquotedKey" `Lake.Toml.unquotedKey unquotedKeyFn

def basicString : Parser :=
  litWithAntiquot "basicString" `Lake.Toml.basicString basicStringFn

def literalString : Parser :=
  litWithAntiquot "literalString" `Lake.Toml.literalString literalStringFn

def mlBasicString : Parser :=
  litWithAntiquot "mlBasicString" `Lake.Toml.mlBasicString mlBasicStringFn

def mlLiteralString : Parser :=
  litWithAntiquot "mlLiteralString" `Lake.Toml.mlLiteralString mlLiteralStringFn

def quotedKey : Parser :=
  basicString <|> literalString

def simpleKey : Parser := nodeWithAntiquot "simpleKey" `Lake.Toml.simpleKey $
  unquotedKey <|> quotedKey

def key : Parser := nodeWithAntiquot "key" `Lake.Toml.key $ setExpected ["key"] $
  sepBy1 simpleKey "." (trailingWs >> chAtom '.' >> trailingWs)

def stdTable : Parser :=
  atomic (chAtom '[' ["table"] >> notFollowedBy (chAtom '[') "'['") >>
  trailingWs >> key >> trailingWs >> chAtom ']'

def arrayTable : Parser :=
  atomic (chAtom '[' ["table"] >> chAtom '[' ) >>
  trailingWs >> key >> trailingWs >> chAtom ']' >> chAtom ']'

def table :=
  stdTable <|> arrayTable

def keyvalCore (val : Parser) : Parser :=
  node `Lake.Toml.keyval $
  key >> trailingWs >> chAtom '=' >> trailingWs >> val

def expressionCore (val : Parser) : Parser :=
  nodeWithAntiquot "expression" `Lake.Toml.expression $
  (keyvalCore val <|> table) >> trailingSep

def header : Parser :=
  litWithAntiquot "header" `Lake.Toml.header skipFn trailingFn

def tomlCore (val : Parser) : Parser :=
  withCache `Lake.Toml.toml $
  nodeWithAntiquot "toml" `Lake.Toml.toml $
  header >> sepBy1Linebreak (expressionCore val)

def inlineTableCore (val : Parser) : Parser := nodeWithAntiquot "inlineTable" `Lake.Toml.inlineTable $
  chAtom '{' ["inline-table"] (trailingFn := trailingFn) >>
  sepBy1 (keyvalCore val >> trailingWs) "," (chAtom ',' (trailingFn := trailingFn)) false >>
  chAtom '}'

def arrayCore (val : Parser) : Parser := nodeWithAntiquot "array" `Lake.Toml.array $
  chAtom '[' ["array"] (trailingFn := trailingFn) >>
  sepBy1 (val >> trailingSep) "," (chAtom ',' (trailingFn := trailingFn)) true >>
  chAtom ']'

def string : Parser :=
  nodeWithAntiquot "string" `Lake.Toml.string $ setExpected ["string"] $
  mlBasicString <|> basicString <|> mlLiteralString <|> literalString

protected def true : Parser :=
  lit `Lake.Toml.true $ strFn "true"

protected def false : Parser :=
  lit `Lake.Toml.false $ strFn "false"

def boolean : Parser :=
  nodeWithAntiquot "boolean" `Lake.Toml.boolean $
  Toml.true <|> Toml.false

def numeralAntiquot :=
  mkAntiquot "float" `Lake.Toml.float (anonymous := false) <|>
  mkAntiquot "decInt" `Lake.Toml.decInt (anonymous := false) <|>
  mkAntiquot "binInt" `Lake.Toml.binInt (anonymous := false) <|>
  mkAntiquot "octInt" `Lake.Toml.octInt (anonymous := false) <|>
  mkAntiquot "hexInt" `Lake.Toml.hexInt (anonymous := false) <|>
  mkAntiquot "dateTime" `Lake.Toml.dateTime (anonymous := false) <|>
  mkAntiquot "numeral" `Lake.Toml.numeral (isPseudoKind := true)

/- A value starting with a numeral. Either a TOML date-time, float, or integer. -/
def numeral : Parser :=
  withAntiquot numeralAntiquot $ dynamicNode numeralFn

def valCore (val : Parser) : Parser :=
  string <|> boolean <|> numeral <|>
  arrayCore val <|> inlineTableCore val

def val : Parser :=
  recNodeWithAntiquot "val" `Lake.Toml.val valCore

def array : Parser :=
  arrayCore val

def inlineTable : Parser :=
  inlineTableCore val

def keyval : Parser :=
  keyvalCore val

def expression : Parser :=
  expressionCore val

def toml : Parser :=
  tomlCore val
