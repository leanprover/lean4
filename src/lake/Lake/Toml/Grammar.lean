/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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

/-- Is it a TOML control character? (excludes tabs and spaces) -/
def isControlChar (c : Char) :=
  c = '\x7F' || (c < '\x20' && c != '\t')

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
  -- While the v1.0.0 TOML ABNF grammar permits a `DEL`, the test suite does not.
  -- We forbid it because it the omission seems likely to be an error
  takeUntilFn isControlChar

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
    let ifStringGap (p : ParserFn) :=
      if stringGap then
        p c (s.next' input s.pos h)
      else
        s.mkUnexpectedError "string gap is forbidden here" expected
    if isEscapeChar curr then
      s.next' input s.pos h
    else if curr == 'u' then
      repeatFn 4 hexDigitFn c (s.next' input s.pos h)
    else if curr == 'U' then
      repeatFn 8 hexDigitFn c (s.next' input s.pos h)
    else if curr == ' ' || curr == '\t' then
      ifStringGap (wsFn >> newlineFn >> wsNewlineFn)
    else if curr == '\n' then
      ifStringGap wsNewlineFn
    else if curr == '\r' then
      ifStringGap (crlfAuxFn >> wsNewlineFn)
    else
      s.mkUnexpectedError "invalid escape sequence"

partial def basicStringAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkUnexpectedErrorAt "unterminated basic string" startPos
  else
    let curr := input.get' s.pos h
    if curr == '\"' then
      s.next' input s.pos h
    else if curr == '\\' then
      (escapeSeqFn false >> basicStringAuxFn startPos) c (s.next' input s.pos h)
    else if isControlChar curr then
      mkUnexpectedCharError s curr
    else
      basicStringAuxFn startPos c (s.next' input s.pos h)

def basicStringFn : ParserFn := usePosFn fun startPos =>
  chFn '\"' ["basic string"] >> basicStringAuxFn startPos

partial def literalStringAuxFn (startPos : String.Pos) : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    s.mkUnexpectedErrorAt "unterminated literal string" startPos
  else
    let curr := input.get' s.pos h
    if curr == '\'' then
      s.next' input s.pos h
    else if isControlChar curr then
      mkUnexpectedCharError s curr
    else
      literalStringAuxFn startPos c (s.next' input s.pos h)

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
    else if curr == '\n' then
      mlLiteralStringAuxFn startPos 0 c (s.next' input s.pos h)
    else if curr == '\r' then
      (crlfAuxFn >> mlLiteralStringAuxFn startPos 0) c (s.next' input s.pos h)
    else if isControlChar curr then
      mkUnexpectedCharError s curr
    else
      mlLiteralStringAuxFn startPos 0 c (s.next' input s.pos h)

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
    else if curr == '\n' then
      mlBasicStringAuxFn startPos 0 c (s.next' input s.pos h)
    else if curr == '\r' then
      (crlfAuxFn >> mlBasicStringAuxFn startPos 0) c (s.next' input s.pos h)
    else if curr == '\\' then
      (escapeSeqFn true >> mlBasicStringAuxFn startPos 0) c (s.next' input s.pos h)
    else if isControlChar curr then
      mkUnexpectedCharError s curr
    else
      mlBasicStringAuxFn startPos 0 c (s.next' input s.pos h)

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

def optTimeFn : ParserFn := fun c s =>
  let i := s.pos
  let input := c.input
  if h : input.atEnd i then
    s
  else
    let curr := input.get' i h
    if curr = 'T' || curr = 't' then
      timeFn true c (s.next' input i h)
    else if curr = ' ' then
      let tPos := input.next' i h
      let s := timeFn true c (s.setPos tPos)
      if s.hasError && s.pos == tPos then s.restore (s.stackSize-1) i else s
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

def decNumberTailAuxFn (startPos : String.Pos) (curr : Char) (nextPos : String.Pos) : ParserFn := fun c s =>
  if curr == '.' then
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

def decNumberTailFn (startPos : String.Pos)  : ParserFn := fun c s =>
  let input := c.input
  if h : input.atEnd s.pos then
    pushLit `Lake.Toml.decInt startPos skipFn c s
  else
    decNumberTailAuxFn startPos (input.get' s.pos h) (input.next' s.pos h) c s

mutual

partial def decNumberSepFn (startPos : String.Pos) (curr : Char) (nextPos : String.Pos) : ParserFn := fun c s =>
  if curr == '_' then
    let s := s.setPos nextPos
    decNumberFn startPos c s
  else
    decNumberTailAuxFn startPos curr nextPos c s

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
    if curr == '0' then
      decNumberTailFn startPos c (s.next' input s.pos h)
    else if curr.isDigit then
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
          pushLit `Lake.Toml.dateTime startPos skipFn c s
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

def numeralFn : ParserFn := atomicFn fun c s =>
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
          pushLit `Lake.Toml.binNum startPos skipFn c s
        else if curr == 'o' then
          let s := s.next' input s.pos h
          let s := sepByChar1Fn isOctDigit '_' ["octal integer"] c s
          if s.hasError then s else
          pushLit `Lake.Toml.octNum startPos skipFn c s
        else if curr == 'x' then
          let s := s.next' input s.pos h
          let s := sepByChar1Fn isHexDigit '_' ["hexadecimal integer"] c s
          if s.hasError then s else
          pushLit `Lake.Toml.hexNum startPos skipFn c s
        else if curr.isDigit then
          let s := s.next' input s.pos h
          let s := (chFn ':' >> timeAuxFn false) c s
          if s.hasError then s else
          pushLit `Lake.Toml.dateTime startPos skipFn c s
        else
          decNumberTailAuxFn startPos curr (input.next' s.pos h) c s
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

def simpleKey : Parser := nodeWithAntiquot "simpleKey" `Lake.Toml.simpleKey (anonymous := true) $
  unquotedKey <|> quotedKey

def key : Parser := nodeWithAntiquot "key" `Lake.Toml.key (anonymous := true)  $ setExpected ["key"]  $
  sepBy1 simpleKey "." (trailingWs >> chAtom '.' >> trailingWs)

def stdTable : Parser := nodeWithAntiquot "stdTable" `Lake.Toml.stdTable $
  atomic (chAtom '[' ["table"] >> notFollowedBy (chAtom '[') "'['") >>
  trailingWs >> key >> trailingWs >> chAtom ']'

def arrayTable : Parser := nodeWithAntiquot "arrayTable" `Lake.Toml.arrayTable $
  atomic (chAtom '[' ["table"] >> chAtom '[' ) >>
  trailingWs >> key >> trailingWs >> chAtom ']' >> chAtom ']'

def table :=
  stdTable <|> arrayTable

def keyvalCore (val : Parser) : Parser := nodeWithAntiquot "keyval" `Lake.Toml.keyval (anonymous := true) $
  key >> trailingWs >> chAtom '=' >> trailingWs >> val

def expressionCore (val : Parser) : Parser :=
  withAntiquot (mkAntiquot "expression" `Lake.Toml.expression (isPseudoKind := true)) $
  keyvalCore val <|> table

def header : Parser :=
  litWithAntiquot "header" `Lake.Toml.header skipFn trailingFn

def tomlCore (val : Parser) : Parser :=
  nodeWithAntiquot "toml" `Lake.Toml.toml (anonymous := true) $
  header >> sepByLinebreak (expressionCore val >> trailingSep)

def inlineTableCore (val : Parser) : Parser := nodeWithAntiquot "inlineTable" `Lake.Toml.inlineTable $
  chAtom '{' ["inline-table"] (trailingFn := trailingFn) >>
  sepBy (keyvalCore val >> trailingWs) "," (chAtom ',' (trailingFn := wsFn)) false >>
  chAtom '}'

def arrayCore (val : Parser) : Parser := nodeWithAntiquot "array" `Lake.Toml.array $
  chAtom '[' ["array"] (trailingFn := trailingFn) >>
  sepBy (val >> trailingSep) "," (chAtom ',' (trailingFn := trailingFn)) true >>
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
  mkAntiquot "binNum" `Lake.Toml.binNum (anonymous := false) <|>
  mkAntiquot "octNum" `Lake.Toml.octNum (anonymous := false) <|>
  mkAntiquot "hexNum" `Lake.Toml.hexNum (anonymous := false) <|>
  mkAntiquot "dateTime" `Lake.Toml.dateTime (anonymous := false) <|>
  mkAntiquot "numeral" `Lake.Toml.numeral (isPseudoKind := true)

/- A value starting with a numeral. Either a TOML date-time, float, or integer. -/
def numeral : Parser :=
  withAntiquot numeralAntiquot $ dynamicNode numeralFn

def numeralOfKind (name : String) (kind : SyntaxNodeKind) : Parser :=
  numeral >> setExpected [name] (checkStackTop (·.isOfKind kind) "illegal numeral kind")

def float : Parser :=
  numeralOfKind "float" `Lake.Toml.float

def decInt : Parser :=
  numeralOfKind "decimal integer" `Lake.Toml.decInt

def binNum : Parser :=
  numeralOfKind "binary number" `Lake.Toml.binNum

def octNum : Parser :=
  numeralOfKind "octal number" `Lake.Toml.octNum

def hexNum : Parser :=
  numeralOfKind "hexadecimal number" `Lake.Toml.hexNum

def dateTime : Parser :=
  numeralOfKind "date-time" `Lake.Toml.dateTime

def valCore (val : Parser) : Parser :=
  string <|> boolean <|> numeral <|>
  arrayCore val <|> inlineTableCore val

def val : Parser :=
  recNodeWithAntiquot "val" `Lake.Toml.val valCore (anonymous := true)

def array : Parser :=
  arrayCore val

def inlineTable : Parser :=
  inlineTableCore val

def keyval : Parser :=
  keyvalCore val

def expression : Parser :=
  expressionCore val

@[run_parser_attribute_hooks] def toml : Parser :=
  withCache `Lake.Toml.toml $ tomlCore val
