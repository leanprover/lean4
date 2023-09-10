import Lean.Parser.Basic

/-! Tokenization functions used for the implementation of the Lean language. -/

namespace Lean.Parser

variable (pushMissingOnError : Bool) in
partial def finishCommentBlock (nesting : Nat) : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then eoi s
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr == '-' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '/' then -- "-/" end of comment
          if nesting == 1 then s.next' input i h
          else finishCommentBlock (nesting-1) c (s.next' input i h)
        else
          finishCommentBlock nesting c (s.setPos i)
    else if curr == '/' then
      if h : input.atEnd i then eoi s
      else
        let curr := input.get' i h
        if curr == '-' then finishCommentBlock (nesting+1) c (s.next' input i h)
        else finishCommentBlock nesting c (s.setPos i)
    else finishCommentBlock nesting c (s.setPos i)
where
  eoi s := s.mkUnexpectedError (pushMissing := pushMissingOnError) "unterminated comment"

/-- Consume whitespace and comments -/
partial def whitespace : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s
  else
    let curr := input.get' i h
    if curr == '\t' then
      s.mkUnexpectedError (pushMissing := false) "tabs are not allowed; please configure your editor to expand them"
    else if curr.isWhitespace then whitespace c (s.next' input i h)
    else if curr == '-' then
      let i    := input.next' i h
      let curr := input.get i
      if curr == '-' then andthenTokenFn (takeUntilFn (fun c => c = '\n')) whitespace c (s.next input i)
      else s
    else if curr == '/' then
      let i        := input.next' i h
      let curr     := input.get i
      if curr == '-' then
        let i    := input.next i
        let curr := input.get i
        if curr == '-' || curr == '!' then s -- "/--" and "/-!" doc comment are actual tokens
        else andthenTokenFn (finishCommentBlock (pushMissingOnError := false) 1) whitespace c (s.next input i)
      else s
    else s

def hexDigitFn : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    let i    := input.next' i h
    if curr.isDigit || ('a' <= curr && curr <= 'f') || ('A' <= curr && curr <= 'F') then s.setPos i
    else s.mkUnexpectedError "invalid hexadecimal numeral"

def quotedCharCoreFn (isQuotable : Char → Bool) : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    if isQuotable curr then
      s.next' input i h
    else if curr == 'x' then
      andthenTokenFn hexDigitFn hexDigitFn c (s.next' input i h)
    else if curr == 'u' then
      andthenTokenFn hexDigitFn (andthenTokenFn hexDigitFn (andthenTokenFn hexDigitFn hexDigitFn)) c (s.next' input i h)
    else
      s.mkUnexpectedError "invalid escape sequence"

def isQuotableCharDefault (c : Char) : Bool :=
  c == '\\' || c == '\"' || c == '\'' || c == 'r' || c == 'n' || c == 't'

def quotedCharFn : TokenParserFn :=
  quotedCharCoreFn isQuotableCharDefault

def charLitFnAux (startPos : String.Pos) : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkEOIError
  else
    let curr := input.get' i h
    let s    := s.setPos (input.next' i h)
    let s    := if curr == '\\' then quotedCharFn c s else s
    if s.hasError then s
    else
      let i    := s.pos
      let curr := input.get i
      let s    := s.setPos (input.next i)
      if curr == '\'' then mkNodeToken charLitKind startPos whitespace c s
      else s.mkUnexpectedError "missing end of character literal"

partial def strLitFnAux (startPos : String.Pos) : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if h : input.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := input.get' i h
    let s    := s.setPos (input.next' i h)
    if curr == '\"' then
      mkNodeToken strLitKind startPos whitespace c s
    else if curr == '\\' then andthenTokenFn quotedCharFn (strLitFnAux startPos) c s
    else strLitFnAux startPos c s

def decimalNumberFn (startPos : String.Pos) : TokenParserFn := fun c s =>
  let s     := takeWhileFn (fun c => c.isDigit) c s
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '.' || curr == 'e' || curr == 'E' then
    let s := parseOptDot c s
    let s := parseOptExp c s
    mkNodeToken scientificLitKind startPos whitespace c s
  else
    mkNodeToken numLitKind startPos whitespace c s
where
  parseOptDot c s :=
    let input := c.input
    let i     := s.pos
    let curr  := input.get i
    if curr == '.' then
      let i    := input.next i
      let curr := input.get i
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else
        s.setPos i
    else
      s

  parseOptExp c s :=
    let input := c.input
    let i     := s.pos
    let curr  := input.get i
    if curr == 'e' || curr == 'E' then
      let i    := input.next i
      let i    := if input.get i == '-' || input.get i == '+' then input.next i else i
      let curr := input.get i
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else
        s.mkUnexpectedError "missing exponent digits in scientific literal"
    else
      s

def binNumberFn (startPos : String.Pos) : TokenParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "binary number" c s
  mkNodeToken numLitKind startPos whitespace c s

def octalNumberFn (startPos : String.Pos) : TokenParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "octal number" c s
  mkNodeToken numLitKind startPos whitespace c s

def hexNumberFn (startPos : String.Pos) : TokenParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" c s
  mkNodeToken numLitKind startPos whitespace c s

def numberFnAux : TokenParserFn := fun c s =>
  let input    := c.input
  let startPos := s.pos
  if h : input.atEnd startPos then s.mkEOIError
  else
    let curr := input.get' startPos h
    if curr == '0' then
      let i    := input.next' startPos h
      let curr := input.get i
      if curr == 'b' || curr == 'B' then
        binNumberFn startPos c (s.next input i)
      else if curr == 'o' || curr == 'O' then
        octalNumberFn startPos c (s.next input i)
      else if curr == 'x' || curr == 'X' then
        hexNumberFn startPos c (s.next input i)
      else
        decimalNumberFn startPos c (s.setPos i)
    else if curr.isDigit then
      decimalNumberFn startPos c (s.next input startPos)
    else
      s.mkError "numeral"

def isIdCont : String → ParserState → Bool := fun input s =>
  let i    := s.pos
  let curr := input.get i
  if curr == '.' then
    let i := input.next i
    if input.atEnd i then
      false
    else
      let curr := input.get i
      isIdFirst curr || isIdBeginEscape curr
  else
    false

private def isToken (idStartPos idStopPos : String.Pos) (tk : Option Token) : Bool :=
  match tk with
  | none    => false
  | some tk =>
     -- if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
    tk.endPos ≥ idStopPos - idStartPos

def mkTokenAndFixPos (startPos : String.Pos) (tk : Option Token) : TokenParserFn := fun c s =>
  match tk with
  | none    => s.mkErrorAt "token" startPos
  | some tk =>
    if c.forbiddenTk? == some tk then
      s.mkErrorAt "forbidden token" startPos
    else
      let stopPos := startPos + tk
      let s       := s.setPos stopPos
      pushToken (fun _ info => mkAtom info tk) startPos whitespace c s

def mkIdResult (startPos : String.Pos) (tk : Option Token) (val : Name) : TokenParserFn := fun c s =>
  let stopPos           := s.pos
  if isToken startPos stopPos tk then
    mkTokenAndFixPos startPos tk c s
  else
    pushToken (fun ss info => mkIdent info ss val) startPos whitespace c s

partial def identFnAux (startPos : String.Pos) (tk : Option Token) (r : Name) : TokenParserFn :=
  let rec parse (r : Name) (c s) :=
    let input := c.input
    let i     := s.pos
    if h : input.atEnd i then
      s.mkEOIError
    else
      let curr := input.get' i h
      if isIdBeginEscape curr then
        let startPart := input.next' i h
        let s         := takeUntilFn isIdEndEscape c (s.setPos startPart)
        if h : input.atEnd s.pos then
          s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
        else
          let stopPart  := s.pos
          let s         := s.next' c.input s.pos h
          let r := .str r (input.extract startPart stopPart)
          if isIdCont input s then
            let s := s.next input s.pos
            parse r c s
          else
            mkIdResult startPos tk r c s
      else if isIdFirst curr then
        let startPart := i
        let s         := takeWhileFn isIdRest c (s.next input i)
        let stopPart  := s.pos
        let r := .str r (input.extract startPart stopPart)
        if isIdCont input s then
          let s := s.next input s.pos
          parse r c s
        else
          mkIdResult startPos tk r c s
      else
        mkTokenAndFixPos startPos tk c s
  parse r

private def isIdFirstOrBeginEscape (c : Char) : Bool :=
  isIdFirst c || isIdBeginEscape c

private def nameLitAux (startPos : String.Pos) : TokenParserFn := fun c s =>
  let input := c.input
  let s     := identFnAux startPos none .anonymous c (s.next input startPos)
  if s.hasError then
    s
  else
    let stx := s.stxStack.back
    match stx with
    | .ident info rawStr _ _ =>
      let s := s.popSyntax
      s.pushSyntax (Syntax.mkNameLit rawStr.toString info)
    | _ => s.mkError "invalid Name literal"

def tokenFnCore : TokenParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '\"' then
    strLitFnAux i c (s.next input i)
  else if curr == '\'' && getNext input i != '\'' then
    charLitFnAux i c (s.next input i)
  else if curr.isDigit then
    numberFnAux c s
  else if curr == '`' && isIdFirstOrBeginEscape (getNext input i) then
    nameLitAux i c s
  else
    let (_, tk) := c.tokens.matchPrefix input i
    identFnAux i tk .anonymous c s

/-- Treat keywords as identifiers. -/
def rawIdentFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError
  else identFnAux i none .anonymous c.toTokenParserContext s

def rawIdentNoAntiquot : Parser := {
  fn := rawIdentFn
}

def fieldIdxFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let curr     := c.input.get iniPos
  if curr.isDigit && curr != '0' then
    let s     := takeWhileFn (fun c => c.isDigit) c.toTokenParserContext s
    mkNodeToken fieldIdxKind iniPos whitespace c.toTokenParserContext s
  else
    s.mkErrorAt "field index" iniPos initStackSz

def fieldIdx : Parser :=
  withAntiquot (mkAntiquot "fieldIdx" `fieldIdx) {
    fn   := fieldIdxFn
    info := mkAtomicInfo "fieldIdx"
  }
