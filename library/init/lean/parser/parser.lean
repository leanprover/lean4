/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import init.lean.position
import init.lean.syntax
import init.lean.toexpr
import init.lean.environment
import init.lean.attributes
import init.lean.parser.trie
import init.lean.parser.identifier
import init.lean.compiler.initattr

namespace Lean
namespace Parser

/- Maximum standard precedence. This is the precedence of Function application.
   In the standard Lean language, only the token `.` has a left-binding power greater
   than `maxPrec` (so that field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
   not `(g (h x)).f`). -/
def maxPrec : Nat := 1024

structure TokenConfig :=
(val : String)
(lbp : Option Nat := none)

namespace TokenConfig

def beq : TokenConfig → TokenConfig → Bool
| ⟨val₁, lbp₁⟩ ⟨val₂, lbp₂⟩ := val₁ == val₂ && lbp₁ == lbp₂

instance : HasBeq TokenConfig :=
⟨beq⟩

def toStr : TokenConfig → String
| ⟨val, some lbp⟩ := val ++ ":" ++ toString lbp
| ⟨val, none⟩     := val

instance : HasToString TokenConfig := ⟨toStr⟩

end TokenConfig

structure TokenCacheEntry :=
(startPos stopPos : String.Pos := 0)
(token : Syntax := Syntax.missing)

structure ParserCache :=
(tokenCache : TokenCacheEntry := {})

def initCacheForInput (input : String) : ParserCache :=
{ tokenCache := { startPos := input.bsize + 1 /- make sure it is not a valid position -/} }

structure ParserContext :=
(env      : Environment)
(input    : String)
(filename : String)
(fileMap  : FileMap)
(tokens   : Trie TokenConfig)

structure ParserState :=
(stxStack : Array Syntax := Array.empty)
(pos      : String.Pos := 0)
(cache    : ParserCache := {})
(errorMsg : Option String := none)

namespace ParserState

@[inline] def hasError (s : ParserState) : Bool :=
s.errorMsg != none

@[inline] def stackSize (s : ParserState) : Nat :=
s.stxStack.size

def restore (s : ParserState) (iniStackSz : Nat) (iniPos : Nat) : ParserState :=
{ stxStack := s.stxStack.shrink iniStackSz, errorMsg := none, pos := iniPos, .. s}

def setPos (s : ParserState) (pos : Nat) : ParserState :=
{ pos := pos, .. s }

def setCache (s : ParserState) (cache : ParserCache) : ParserState :=
{ cache := cache, .. s }

def pushSyntax (s : ParserState) (n : Syntax) : ParserState :=
{ stxStack := s.stxStack.push n, .. s }

def popSyntax (s : ParserState) : ParserState :=
{ stxStack := s.stxStack.pop, .. s }

def shrinkStack (s : ParserState) (iniStackSz : Nat) : ParserState :=
{ stxStack := s.stxStack.shrink iniStackSz, .. s }

def next (s : ParserState) (input : String) (pos : Nat) : ParserState :=
{ pos := input.next pos, .. s }

def toErrorMsg (ctx : ParserContext) (s : ParserState) : String :=
match s.errorMsg with
| none     => ""
| some msg =>
  let pos := ctx.fileMap.toPosition s.pos;
  ctx.filename ++ ":" ++ toString pos.line ++ ":" ++ toString pos.column ++ " " ++ msg

def mkNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, err⟩ =>
  if err != none && stack.size == iniStackSz then
    -- If there is an error but there are no new nodes on the stack, we just return `d`
    s
  else
    let newNode := Syntax.node k (stack.extract iniStackSz stack.size) [];
    let stack   := stack.shrink iniStackSz;
    let stack   := stack.push newNode;
    ⟨stack, pos, cache, err⟩

def mkError (s : ParserState) (msg : String) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ => ⟨stack, pos, cache, some msg⟩

def mkEOIError (s : ParserState) : ParserState :=
s.mkError "end of input"

def mkErrorAt (s : ParserState) (msg : String) (pos : String.Pos) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack, pos, cache, some msg⟩

end ParserState

inductive ParserKind
| leading | trailing

export ParserKind (leading trailing)

def ParserArg : ParserKind → Type
| ParserKind.leading := Nat
| ParserKind.trailing := Syntax

def BasicParserFn := ParserContext → ParserState → ParserState

def ParserFn (k : ParserKind) := ParserArg k → BasicParserFn

instance ParserFn.inhabited (k : ParserKind) : Inhabited (ParserFn k) := ⟨fun _ _ => id⟩

inductive FirstTokens
| epsilon : FirstTokens
| unknown : FirstTokens
| tokens  : List TokenConfig → FirstTokens

namespace FirstTokens

def merge : FirstTokens → FirstTokens → FirstTokens
| epsilon     tks         := tks
| tks         epsilon     := tks
| (tokens s₁) (tokens s₂) := tokens (s₁ ++ s₂)
| _           _           := unknown

def seq : FirstTokens → FirstTokens → FirstTokens
| epsilon tks := tks
| tks     _   := tks

def toStr : FirstTokens → String
| epsilon      := "epsilon"
| unknown      := "unknown"
| (tokens tks) := toString tks

instance : HasToString FirstTokens := ⟨toStr⟩

end FirstTokens

structure ParserInfo :=
(updateTokens : Trie TokenConfig → ExceptT String Id (Trie TokenConfig) := fun tks => pure tks)
(firstTokens  : FirstTokens := FirstTokens.unknown)

structure Parser (k : ParserKind := leading) :=
(info : ParserInfo := {})
(fn   : ParserFn k)

instance Parser.inhabited {k : ParserKind} : Inhabited (Parser k) :=
⟨{ fn := fun _ _ s => s }⟩

abbrev TrailingParser := Parser trailing

@[noinline] def epsilonInfo : ParserInfo :=
{ firstTokens := FirstTokens.epsilon }

@[inline] def pushLeadingFn : ParserFn trailing :=
fun a c s => s.pushSyntax a

@[inline] def pushLeading : TrailingParser :=
{ info := epsilonInfo,
  fn   := pushLeadingFn }

@[inline] def checkLeadingFn (p : Syntax → Bool) : ParserFn trailing :=
fun a c s =>
  if p a then s
  else s.mkError "invalid leading token"

@[inline] def checkLeading (p : Syntax → Bool) : TrailingParser :=
{ info := epsilonInfo,
  fn   := checkLeadingFn p }

@[inline] def andthenAux (p q : BasicParserFn) : BasicParserFn :=
fun c s =>
  let s := p c s;
  if s.hasError then s else q c s

@[inline] def andthenFn {k : ParserKind} (p q : ParserFn k) : ParserFn k :=
fun a c s => andthenAux (p a) (q a) c s

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := fun tks => q.updateTokens tks >>= p.updateTokens,
  firstTokens  := p.firstTokens.seq q.firstTokens }

@[inline] def andthen {k : ParserKind} (p q : Parser k) : Parser k :=
{ info := andthenInfo p.info q.info,
  fn   := andthenFn p.fn q.fn }

instance hashAndthen {k : ParserKind} : HasAndthen (Parser k) :=
⟨andthen⟩

@[inline] def nodeFn {k : ParserKind} (n : SyntaxNodeKind) (p : ParserFn k) : ParserFn k
| a c s :=
  let iniSz := s.stackSize;
  let s     := p a c s;
  s.mkNode n iniSz

@[noinline] def nodeInfo (p : ParserInfo) : ParserInfo :=
{ updateTokens := p.updateTokens,
  firstTokens  := p.firstTokens }

@[inline] def node {k : ParserKind} (n : SyntaxNodeKind) (p : Parser k) : Parser k :=
{ info := nodeInfo p.info,
  fn   := nodeFn n p.fn }

@[inline] def leadingNode (n : SyntaxNodeKind) (p : Parser leading) : Parser :=
node n p

@[inline] def trailingNode (n : SyntaxNodeKind) (p : Parser trailing) : TrailingParser :=
node n p

@[inline] def orelseFn {k : ParserKind} (p q : ParserFn k) : ParserFn k
| a c s :=
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  if s.hasError && s.pos == iniPos then q a c (s.restore iniSz iniPos) else s

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := fun tks => q.updateTokens tks >>= p.updateTokens,
  firstTokens  := p.firstTokens.merge q.firstTokens }

@[inline] def orelse {k : ParserKind} (p q : Parser k) : Parser k :=
{ info := orelseInfo p.info q.info,
  fn   := orelseFn p.fn q.fn }

instance hashOrelse {k : ParserKind} : HasOrelse (Parser k) :=
⟨orelse⟩

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ updateTokens := info.updateTokens }

@[inline] def tryFn {k : ParserKind} (p : ParserFn k ) : ParserFn k
| a c s :=
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  match p a c s with
  | ⟨stack, _, cache, some msg⟩ => ⟨stack.shrink iniSz, iniPos, cache, some msg⟩
  | other                       => other

@[inline] def try {k : ParserKind} (p : Parser k) : Parser k :=
{ info := noFirstTokenInfo p.info,
  fn   := tryFn p.fn }

@[inline] def optionalFn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s;
  s.mkNode nullKind iniSz

@[inline] def optional {k : ParserKind} (p : Parser k) : Parser k :=
{ info := noFirstTokenInfo p.info,
  fn   := optionalFn p.fn }

@[specialize] partial def manyAux {k : ParserKind} (p : ParserFn k) : ParserFn k
| a c s :=
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  if s.hasError then s.restore iniSz iniPos
  else if iniPos == s.pos then s.mkError "invalid 'many' parser combinator application, parser did not consume anything"
  else manyAux a c s

@[inline] def manyFn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let s := manyAux p a c s;
  s.mkNode nullKind iniSz

@[inline] def many {k : ParserKind} (p : Parser k) : Parser k :=
{ info := noFirstTokenInfo p.info,
  fn   := manyFn p.fn }

@[inline] def many1Fn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let s := andthenFn p (manyAux p) a c s;
  s.mkNode nullKind iniSz

@[inline] def many1 {k : ParserKind} (p : Parser k) : Parser k :=
{ info := p.info,
  fn   := many1Fn p.fn }

@[specialize] private partial def sepByFnAux {k : ParserKind} (p : ParserFn k) (sep : ParserFn k) (allowTrailingSep : Bool) (iniSz : Nat) : Bool → ParserFn k
| pOpt a c s :=
  let sz  := s.stackSize;
  let pos := s.pos;
  let s   := p a c s;
  if s.hasError then
    if pOpt then
      let s := s.restore sz pos;
      s.mkNode nullKind iniSz
    else
      -- append `Syntax.missing` to make clear that List is incomplete
      let s := s.pushSyntax Syntax.missing;
      s.mkNode nullKind iniSz
  else
    let sz  := s.stackSize;
    let pos := s.pos;
    let s   := sep a c s;
    if s.hasError then
      let s := s.restore sz pos;
      s.mkNode nullKind iniSz
    else
      sepByFnAux allowTrailingSep a c s

@[specialize] def sepByFn {k : ParserKind} (allowTrailingSep : Bool) (p : ParserFn k) (sep : ParserFn k) : ParserFn k
| a c s :=
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz true a c s

@[specialize] def sepBy1Fn {k : ParserKind} (allowTrailingSep : Bool) (p : ParserFn k) (sep : ParserFn k) : ParserFn k
| a c s :=
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz false a c s

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo :=
{ updateTokens := fun tks => p.updateTokens tks >>= sep.updateTokens }

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo :=
{ updateTokens := fun tks => p.updateTokens tks >>= sep.updateTokens,
  firstTokens  := p.firstTokens }

@[inline] def sepBy {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) : Parser k :=
{ info := sepByInfo p.info sep.info,
  fn   := sepByFn allowTrailingSep p.fn sep.fn }

@[inline] def sepBy1 {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) : Parser k :=
{ info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn }

@[specialize] partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : BasicParserFn
| c s :=
  let i := s.pos;
  if c.input.atEnd i then s.mkEOIError
  else if p (c.input.get i) then s.next c.input i
  else s.mkError errorMsg

@[specialize] partial def takeUntilFn (p : Char → Bool) : BasicParserFn
| c s :=
  let i := s.pos;
  if c.input.atEnd i then s
  else if p (c.input.get i) then s
  else takeUntilFn c (s.next c.input i)

@[specialize] def takeWhileFn (p : Char → Bool) : BasicParserFn :=
takeUntilFn (fun c => !p c)

@[inline] def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : BasicParserFn :=
andthenAux (satisfyFn p errorMsg) (takeWhileFn p)

partial def finishCommentBlock : Nat → BasicParserFn
| nesting c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let i    := input.next i;
    if curr == '-' then
      if input.atEnd i then s.mkEOIError
      else
        let curr := input.get i;
        if curr == '/' then -- "-/" end of comment
          if nesting == 1 then s.next input i
          else finishCommentBlock (nesting-1) c (s.next input i)
        else
          finishCommentBlock nesting c (s.next input i)
    else if curr == '/' then
      if input.atEnd i then s.mkEOIError
      else
        let curr := input.get i;
        if curr == '-' then finishCommentBlock (nesting+1) c (s.next input i)
        else finishCommentBlock nesting c (s.setPos i)
    else finishCommentBlock nesting c (s.setPos i)

/- Consume whitespace and comments -/
partial def whitespace : BasicParserFn
| c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s
  else
    let curr := input.get i;
    if curr.isWhitespace then whitespace c (s.next input i)
    else if curr == '-' then
      let i    := input.next i;
      let curr := input.get i;
      if curr == '-' then andthenAux (takeUntilFn (fun c => c = '\n')) whitespace c (s.next input i)
      else s
    else if curr == '/' then
      let i    := input.next i;
      let curr := input.get i;
      if curr == '-' then
        let i    := input.next i;
        let curr := input.get i;
        if curr == '-' then s -- "/--" doc comment is an actual token
        else andthenAux (finishCommentBlock 1) whitespace c (s.next input i)
      else s
    else s

def mkEmptySubstringAt (s : String) (p : Nat) : Substring :=
{str := s, startPos := p, stopPos := p }

private def rawAux {k : ParserKind} (startPos : Nat) (trailingWs : Bool) : ParserFn k
| a c s :=
  let input   := c.input;
  let stopPos := s.pos;
  let leading := mkEmptySubstringAt input startPos;
  let val     := input.extract startPos stopPos;
  if trailingWs then
    let s        := whitespace c s;
    let stopPos' := s.pos;
    let trailing := { Substring . str := input, startPos := stopPos, stopPos := stopPos' };
    let atom     := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val;
    s.pushSyntax atom
  else
    let trailing := mkEmptySubstringAt input stopPos;
    let atom := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val;
    s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
@[inline] def rawFn {k : ParserKind} (p : ParserFn k) (trailingWs := false) : ParserFn k
| a c s :=
  let startPos := s.pos;
  let s := p a c s;
  if s.hasError then s else rawAux startPos trailingWs a c s

def hexDigitFn : BasicParserFn
| c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let i    := input.next i;
    if curr.isDigit || ('a' <= curr && curr <= 'f') || ('A' <= curr && curr <= 'F') then s.setPos i
    else s.mkError "invalid hexadecimal numeral, hexadecimal digit expected"

def quotedCharFn : BasicParserFn
| c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    if curr == '\\' || curr == '\"' || curr == '\'' || curr == '\n' || curr == '\t' then
      s.next input i
    else if curr == 'x' then
      andthenAux hexDigitFn hexDigitFn c (s.next input i)
    else if curr == 'u' then
      andthenAux hexDigitFn (andthenAux hexDigitFn (andthenAux hexDigitFn hexDigitFn)) c (s.next input i)
    else
      s.mkError "invalid escape sequence"

/-- Push `(Syntax.node tk <new-atom>)` into syntax stack -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : Nat) : BasicParserFn :=
fun c s =>
let input     := c.input;
let stopPos   := s.pos;
let leading   := mkEmptySubstringAt input startPos;
let val       := input.extract startPos stopPos;
let s         := whitespace c s;
let wsStopPos := s.pos;
let trailing  := { Substring . str := input, startPos := stopPos, stopPos := wsStopPos };
let info      := { SourceInfo . leading := leading, pos := startPos, trailing := trailing };
s.pushSyntax (mkLit n val (some info))

partial def strLitFnAux (startPos : Nat) : BasicParserFn
| c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let s    := s.setPos (input.next i);
    if curr == '\"' then
      mkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenAux quotedCharFn strLitFnAux c s
    else strLitFnAux c s

def decimalNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s     := takeWhileFn (fun c => c.isDigit) c s;
  let input := c.input;
  let i     := s.pos;
  let curr  := input.get i;
  let s :=
    /- TODO(Leo): should we use a different kind for numerals containing decimal points? -/
    if curr == '.' then
      let i    := input.next i;
      let curr := input.get i;
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else s
    else s;
  mkNodeToken numLitKind startPos c s

def binNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "expected binary number" c s;
  mkNodeToken numLitKind startPos c s

def octalNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "expected octal number" c s;
  mkNodeToken numLitKind startPos c s

def hexNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "expected hexadecimal number" c s;
  mkNodeToken numLitKind startPos c s

def numberFnAux : BasicParserFn :=
fun c s =>
  let input    := c.input;
  let startPos := s.pos;
  if input.atEnd startPos then s.mkEOIError
  else
    let curr := input.get startPos;
    if curr == '0' then
      let i    := input.next startPos;
      let curr := input.get i;
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
      s.mkError "expected numeral"

def isIdCont : String → ParserState → Bool
| input s :=
  let i    := s.pos;
  let curr := input.get i;
  if curr == '.' then
    let i := input.next i;
    if input.atEnd i then
      false
    else
      let curr := input.get i;
      isIdFirst curr || isIdBeginEscape curr
  else
    false

private def isToken (idStartPos idStopPos : Nat) (tk : Option TokenConfig) : Bool :=
match tk with
| none    => false
| some tk =>
   -- if a token is both a symbol and a valid identifier (i.e. a keyword),
   -- we want it to be recognized as a symbol
  tk.val.bsize ≥ idStopPos - idStopPos

def mkTokenAndFixPos (startPos : Nat) (tk : Option TokenConfig) : BasicParserFn :=
fun c s =>
match tk with
| none    => s.mkErrorAt "token expected" startPos
| some tk =>
  let input     := c.input;
  let leading   := mkEmptySubstringAt input startPos;
  let val       := tk.val;
  let stopPos   := startPos + val.bsize;
  let s         := s.setPos stopPos;
  let s         := whitespace c s;
  let wsStopPos := s.pos;
  let trailing  := { Substring . str := input, startPos := stopPos, stopPos := wsStopPos };
  let atom      := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val;
  s.pushSyntax atom

def mkIdResult (startPos : Nat) (tk : Option TokenConfig) (val : Name) : BasicParserFn :=
fun c s =>
let stopPos              := s.pos;
if isToken startPos stopPos tk then
  mkTokenAndFixPos startPos tk c s
else
  let input           := c.input;
  let rawVal          := { Substring . str := input, startPos := startPos, stopPos := stopPos };
  let s               := whitespace c s;
  let trailingStopPos := s.pos;
  let leading         := mkEmptySubstringAt input startPos;
  let trailing        := { Substring . str := input, startPos := stopPos, stopPos := trailingStopPos };
  let info            := { SourceInfo . leading := leading, trailing := trailing, pos := startPos };
  let atom            := Syntax.ident (some info) rawVal val [] [];
  s.pushSyntax atom

partial def identFnAux (startPos : Nat) (tk : Option TokenConfig) : Name → BasicParserFn
| r c s :=
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    if isIdBeginEscape curr then
      let startPart := input.next i;
      let s         := takeUntilFn isIdEndEscape c (s.setPos startPart);
      let stopPart  := s.pos;
      let s         := satisfyFn isIdEndEscape "end of escaped identifier expected" c s;
      if s.hasError then s
      else
        let r := Name.mkString r (input.extract startPart stopPart);
        if isIdCont input s then
          let s := s.next input s.pos;
          identFnAux r c s
        else
          mkIdResult startPos tk r c s
    else if isIdFirst curr then
      let startPart := i;
      let s         := takeWhileFn isIdRest c (s.next input i);
      let stopPart  := s.pos;
      let r := Name.mkString r (input.extract startPart stopPart);
      if isIdCont input s then
        let s := s.next input s.pos;
        identFnAux r c s
      else
        mkIdResult startPart tk r c s
    else
      mkTokenAndFixPos startPos tk c s

private def tokenFnAux : BasicParserFn
| c s :=
  let input := c.input;
  let i     := s.pos;
  let curr  := input.get i;
  if curr == '\"' then
    strLitFnAux i c (s.next input i)
  else if curr.isDigit then
    numberFnAux c s
  else
    let (_, tk) := c.tokens.matchPrefix input i;
    identFnAux i tk Name.anonymous c s

private def updateCache (startPos : Nat) (s : ParserState) : ParserState :=
match s with
| ⟨stack, pos, cache, none⟩ =>
  if stack.size == 0 then s
  else
    let tk := stack.back;
    ⟨stack, pos, { tokenCache := { startPos := startPos, stopPos := pos, token := tk } }, none⟩
| other => other

def tokenFn : BasicParserFn :=
fun c s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let tkc := s.cache.tokenCache;
    if tkc.startPos == i then
      let s := s.pushSyntax tkc.token;
      s.setPos tkc.stopPos
    else
      let s := tokenFnAux c s;
      updateCache i s

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Option Syntax :=
let iniSz  := s.stackSize;
let iniPos := s.pos;
let s      := tokenFn c s;
if s.hasError then (s.restore iniSz iniPos, none)
else
  let stx := s.stxStack.back;
  (s.restore iniSz iniPos, some stx)

@[inline] def satisfySymbolFn (p : String → Bool) (errorMsg : String) : BasicParserFn :=
fun c s =>
  let startPos := s.pos;
  let s        := tokenFn c s;
  if s.hasError then
    s.mkErrorAt errorMsg startPos
  else
    match s.stxStack.back with
    | Syntax.atom _ sym => if p sym then s else s.mkErrorAt errorMsg startPos
    | _                 => s.mkErrorAt errorMsg startPos

def symbolFnAux (sym : String) (errorMsg : String) : BasicParserFn :=
satisfySymbolFn (fun s => s == sym) errorMsg

def insertToken (sym : String) (lbp : Option Nat) (tks : Trie TokenConfig) : ExceptT String Id (Trie TokenConfig) :=
if sym == "" then throw "invalid empty symbol"
else match tks.find sym, lbp with
| none,       _           => pure (tks.insert sym { val := sym, lbp := lbp })
| some _,     none        => pure tks
| some tk,    some newLbp =>
  match tk.lbp with
  | none        => pure (tks.insert sym { val := sym, lbp := lbp })
  | some oldLbp => if newLbp == oldLbp then pure tks else throw ("precedence mismatch for '" ++ toString sym ++ "', previous: " ++ toString oldLbp ++ ", new: " ++ toString newLbp)

def symbolInfo (sym : String) (lbp : Option Nat) : ParserInfo :=
{ updateTokens := insertToken sym lbp,
  firstTokens  := FirstTokens.tokens [ { val := sym, lbp := lbp } ] }

@[inline] def symbolFn {k : ParserKind} (sym : String) : ParserFn k :=
fun _ => symbolFnAux sym ("expected '" ++ sym ++ "'")

@[inline] def symbol {k : ParserKind} (sym : String) (lbp : Option Nat := none) : Parser k :=
let sym := sym.trim;
{ info := symbolInfo sym lbp,
  fn   := symbolFn sym }

def unicodeSymbolFnAux (sym asciiSym : String) (errorMsg : String) : BasicParserFn :=
satisfySymbolFn (fun s => s == sym || s == asciiSym) errorMsg

def unicodeSymbolInfo (sym asciiSym : String) (lbp : Option Nat) : ParserInfo :=
{ updateTokens := fun tks => insertToken sym lbp tks >>= insertToken asciiSym lbp,
  firstTokens  := FirstTokens.tokens [ { val := sym, lbp := lbp }, { val := asciiSym, lbp := lbp } ] }

@[inline] def unicodeSymbolFn {k : ParserKind} (sym asciiSym : String) : ParserFn k :=
fun _ => unicodeSymbolFnAux sym asciiSym ("expected '" ++ sym ++ "' or '" ++ asciiSym ++ "'")

@[inline] def unicodeSymbol {k : ParserKind} (sym asciiSym : String) (lbp : Option Nat := none) : Parser k :=
{ info := unicodeSymbolInfo sym asciiSym lbp,
  fn   := unicodeSymbolFn sym asciiSym }

def mkAtomicInfo (k : String) : ParserInfo :=
{ firstTokens := FirstTokens.tokens [ { val := k } ] }

def numLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind numLitKind) then s.mkErrorAt "expected numeral" iniPos else s

@[inline] def numLit {k : ParserKind} : Parser k :=
{ fn   := numLitFn,
  info := mkAtomicInfo "numLit" }

def strLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "expected string literal" iniPos else s

@[inline] def strLit {k : ParserKind} : Parser k :=
{ fn   := strLitFn,
  info := mkAtomicInfo "strLit" }

def identFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isIdent) then s.mkErrorAt "expected identifier" iniPos else s

@[inline] def ident {k : ParserKind} : Parser k :=
{ fn   := identFn,
  info := mkAtomicInfo "ident" }

def fieldIdxFn : BasicParserFn :=
fun c s =>
  let iniPos := s.pos;
  let curr     := c.input.get iniPos;
  if curr.isDigit && curr != '0' then
    let s     := takeWhileFn (fun c => c.isDigit) c s;
    mkNodeToken fieldIdxKind iniPos c s
  else
    s.mkErrorAt "expected field index" iniPos

@[inline] def fieldIdx {k : ParserKind} : Parser k :=
{ fn   := fun _ => fieldIdxFn,
  info := mkAtomicInfo "fieldIdx" }

instance string2basic {k : ParserKind} : HasCoe String (Parser k) :=
⟨symbol⟩

namespace ParserState

def keepNewError (s : ParserState) (oldStackSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, err⟩ => ⟨stack.shrink oldStackSize, pos, cache, err⟩

def keepPrevError (s : ParserState) (oldStackSize : Nat) (oldStopPos : String.Pos) (oldError : Option String) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack.shrink oldStackSize, oldStopPos, cache, oldError⟩

def mergeErrors (s : ParserState) (oldStackSize : Nat) (oldError : String) : ParserState :=
match s with
| ⟨stack, pos, cache, some err⟩ =>
  if oldError == err then s
  else ⟨stack.shrink oldStackSize, pos, cache, some (err ++ "; " ++ oldError)⟩
| other                         => other

def mkLongestNodeAlt (s : ParserState) (startSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ =>
  if stack.size == startSize then ⟨stack.push Syntax.missing, pos, cache, none⟩ -- parser did not create any node, then we just add `Syntax.missing`
  else if stack.size == startSize + 1 then s
  else
    -- parser created more than one node, combine them into a single node
    let node := Syntax.node nullKind (stack.extract startSize stack.size) [];
    let stack := stack.shrink startSize;
    ⟨stack.push node, pos, cache, none⟩

def keepLatest (s : ParserState) (startStackSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ =>
  let node  := stack.back;
  let stack := stack.shrink startStackSize;
  let stack := stack.push node;
  ⟨stack, pos, cache, none⟩

def replaceLongest (s : ParserState) (startStackSize : Nat) (prevStackSize : Nat) : ParserState :=
let s := s.mkLongestNodeAlt prevStackSize;
s.keepLatest startStackSize

end ParserState

def longestMatchStep {k : ParserKind} (startSize : Nat) (startPos : String.Pos) (p : ParserFn k) : ParserFn k :=
fun a c s =>
let prevErrorMsg  := s.errorMsg;
let prevStopPos   := s.pos;
let prevSize      := s.stackSize;
let s             := s.restore prevSize startPos;
let s             := p a c s;
match prevErrorMsg, s.errorMsg with
| none, none   => -- both succeeded
  if s.pos > prevStopPos      then s.replaceLongest startSize prevSize -- replace
  else if s.pos < prevStopPos then s.restore prevSize prevStopPos      -- keep prev
  else s.mkLongestNodeAlt prevSize                                     -- keep both
| none, some _ => -- prev succeeded, current failed
  s.restore prevSize prevStopPos
| some oldError, some _ => -- both failed
  if s.pos > prevStopPos      then s.keepNewError prevSize
  else if s.pos < prevStopPos then s.keepPrevError prevSize prevStopPos prevErrorMsg
  else s.mergeErrors prevSize oldError
| some _, none => -- prev failed, current succeeded
  s.mkLongestNodeAlt startSize

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
if !s.hasError && s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux {k : ParserKind} (startSize : Nat) (startPos : String.Pos) : List (Parser k) → ParserFn k
| []      := fun _ _ s => longestMatchMkResult startSize s
| (p::ps) := fun a c s =>
   let s := longestMatchStep startSize startPos p.fn a c s;
   longestMatchFnAux ps a c s

def longestMatchFn₁ {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
let startSize := s.stackSize;
let s := p a c s;
if s.hasError then s else s.mkLongestNodeAlt startSize

def longestMatchFn {k : ParserKind} : List (Parser k) → ParserFn k
| []      := fun _ _ s => s.mkError "longestMatch: empty list"
| [p]     := longestMatchFn₁ p.fn
| (p::ps) := fun a c s =>
  let startSize := s.stackSize;
  let startPos  := s.pos;
  let s         := p.fn a c s;
  if s.hasError then
    let s := s.shrinkStack startSize;
    longestMatchFnAux startSize startPos ps a c s
  else
    let s := s.mkLongestNodeAlt startSize;
    longestMatchFnAux startSize startPos ps a c s

def anyOfFn {k : ParserKind} : List (Parser k) → ParserFn k
| []      _ _ s := s.mkError "anyOf: empty list"
| [p]     a c s := p.fn a c s
| (p::ps) a c s := orelseFn p.fn (anyOfFn ps) a c s

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickLt

namespace TokenMap

def insert {α : Type} (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
match map.find k with
| none    => map.insert k [v]
| some vs => map.insert k (v::vs)

instance {α : Type} : Inhabited (TokenMap α) := ⟨RBMap.empty⟩

instance {α : Type} : HasEmptyc (TokenMap α) := ⟨RBMap.empty⟩

end TokenMap

structure ParsingTables :=
(leadingTable    : TokenMap Parser := {})
(trailingTable   : TokenMap TrailingParser := {})
(trailingParsers : List TrailingParser := []) -- for supporting parsers such as function application
(tokens          : Trie TokenConfig := {})

def currLbp (c : ParserContext) (s : ParserState) : ParserState × Nat :=
let (s, stx) := peekToken c s;
match stx with
| some (Syntax.atom _ sym) =>
  match c.tokens.matchPrefix sym 0 with
  | (_, some tk) => (s, tk.lbp.getOrElse 0)
  | _            => (s, 0)
| some (Syntax.ident _ _ _ _ _) => (s, maxPrec)
| some (Syntax.node k _ _)      => if k == numLitKind || k == strLitKind then (s, maxPrec) else (s, 0)
| _                             => (s, 0)

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) : ParserState × List α :=
let (s, stx) := peekToken c s;
let find (n : Name) : ParserState × List α :=
  match map.find n with
  | some as => (s, as)
  | _       => (s, []);
match stx with
| some (Syntax.atom _ sym)      => find (mkSimpleName sym)
| some (Syntax.ident _ _ _ _ _) => find `ident
| some (Syntax.node k _ _)      => find k
| _                             => (s, [])

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
if s.stackSize == iniSz + 1 then s
else s.mkNode nullKind iniSz -- throw error instead?

def leadingParser (kind : String) (tables : ParsingTables) : ParserFn leading :=
fun a c s =>
  let iniSz   := s.stackSize;
  let (s, ps) := indexed tables.leadingTable c s;
  if ps.isEmpty then
    s.mkError ("expected " ++ kind)
  else
    let s       := longestMatchFn ps a c s;
    mkResult s iniSz

partial def trailingLoop (kind : String) (tables : ParsingTables) (rbp : Nat) (c : ParserContext) : Syntax → ParserState → ParserState
| left s :=
  let (s, lbp) := currLbp c s;
  if rbp ≥ lbp then s.pushSyntax left
  else
    let iniSz   := s.stackSize;
    let (s, ps) := indexed tables.trailingTable c s;
    if ps.isEmpty && tables.trailingParsers.isEmpty then
      s.pushSyntax left -- no available trail
    else
      let s := orelseFn (longestMatchFn ps) (anyOfFn tables.trailingParsers) left c s;
      if s.hasError then s
      else
        let s := mkResult s iniSz;
        let left := s.stxStack.back;
        let s    := s.popSyntax;
        trailingLoop left s

def prattParser (kind : String) (tables : ParsingTables) : ParserFn leading :=
fun rbp c s =>
  let c := { tokens := tables.tokens, .. c };
  let s := leadingParser kind tables rbp c s;
  if s.hasError then s
  else
    let left := s.stxStack.back;
    let s    := s.popSyntax;
    trailingLoop kind tables rbp c left s

def mkParserContext (env : Environment) (input : String) (filename : String) : ParserContext :=
{ env      := env,
  input    := input,
  filename := filename,
  fileMap  := input.toFileMap,
  tokens   := {} }

def mkParserState (input : String) : ParserState :=
{ cache := initCacheForInput input }

def runParser (env : Environment) (tables : ParsingTables) (input : String) (fileName := "<input>") (kind := "<main>") : Except String Syntax :=
let c := mkParserContext env input fileName;
let s := mkParserState input;
let s := prattParser kind tables (0 : Nat) c s;
if s.hasError then
  Except.error (s.toErrorMsg c)
else
  Except.ok s.stxStack.back

def mkBuiltinParsingTablesRef : IO (IO.Ref ParsingTables) :=
IO.mkRef {}

private def updateTokens (tables : ParsingTables) (info : ParserInfo) (declName : Name) : IO ParsingTables :=
match info.updateTokens tables.tokens with
| Except.ok newTokens => pure { tokens := newTokens, .. tables }
| Except.error msg    => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', " ++ msg))

def addBuiltinLeadingParser (tablesRef : IO.Ref ParsingTables) (declName : Name) (p : Parser) : IO Unit :=
do tables ← tablesRef.get;
   tablesRef.reset;
   tables ← updateTokens tables p.info declName;
   match p.info.firstTokens with
   | FirstTokens.tokens tks =>
     let tables := tks.foldl (fun (tables : ParsingTables) tk => { leadingTable := tables.leadingTable.insert (mkSimpleName tk.val) p, .. tables }) tables;
     tablesRef.set tables
   | _ =>
     throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', initial token is not statically known"))

def addBuiltinTrailingParser (tablesRef : IO.Ref ParsingTables) (declName : Name) (p : TrailingParser) : IO Unit :=
do tables ← tablesRef.get;
   tablesRef.reset;
   tables ← updateTokens tables p.info declName;
   match p.info.firstTokens with
   | FirstTokens.tokens tks =>
     let tables := tks.foldl (fun (tables : ParsingTables) tk => { trailingTable := tables.trailingTable.insert (mkSimpleName tk.val) p, .. tables }) tables;
     tablesRef.set tables
   | _ =>
     let tables := { trailingParsers := p :: tables.trailingParsers, .. tables };
     tablesRef.set tables

def declareBuiltinParser (env : Environment) (addFnName : Name) (refDeclName : Name) (declName : Name) : IO Environment :=
let name := `_regBuiltinParser ++ declName;
let type := Expr.app (mkConst `IO) (mkConst `Unit);
let val  := mkCApp addFnName [mkConst refDeclName, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
| none     => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
| some env => IO.ofExcept (setInitAttr env name)

def declareLeadingBuiltinParser (env : Environment) (refDeclName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinLeadingParser refDeclName declName

def declareTrailingBuiltinParser (env : Environment) (refDeclName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinTrailingParser refDeclName declName

/-
The parsing tables for builtin parsers are "stored" in the extracted source code.
-/
def registerBuiltinParserAttribute (attrName : Name) (refDeclName : Name) : IO Unit :=
registerAttribute {
 name  := attrName,
 descr := "Builtin parser",
 add   := fun env declName args persistent => do {
   unless args.isMissing $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', unexpected argument"));
   unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', must be persistent"));
   match env.find declName with
   | none  => throw "unknown declaration"
   | some decl =>
     match decl.type with
     | Expr.const `Lean.Parser.TrailingParser _ =>
       declareTrailingBuiltinParser env refDeclName declName
     | Expr.app (Expr.const `Lean.Parser.Parser _) (Expr.const `Lean.Parser.ParserKind.leading _) =>
       declareLeadingBuiltinParser env refDeclName declName
     | _ =>
       throw (IO.userError ("unexpected parser type at '" ++ toString declName ++ "' (`Parser` or `TrailingParser` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

@[init mkBuiltinParsingTablesRef]
constant builtinCommandParsingTable : IO.Ref ParsingTables := default _

@[init] def regBuiltinCommandParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinCommandParser `Lean.Parser.builtinCommandParsingTable

@[noinline] unsafe def runBuiltinParserUnsafe (kind : String) (ref : IO.Ref ParsingTables) : ParserFn leading :=
fun a c s =>
match unsafeIO (do tables ← ref.get; pure $ prattParser kind tables a c s) with
| some s => s
| none   => s.mkError "failed to access builtin reference"

@[implementedBy runBuiltinParserUnsafe]
constant runBuiltinParser (kind : String) (ref : IO.Ref ParsingTables) : ParserFn leading := default _

def commandParser (rbp : Nat := 0) : Parser :=
{ fn := fun _ => runBuiltinParser "command" builtinCommandParsingTable rbp }

/- TODO(Leo): delete -/
@[init mkBuiltinParsingTablesRef]
constant builtinTestParsingTable : IO.Ref ParsingTables := default _
@[init] def regBuiltinTestParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinTestParser `Lean.Parser.builtinTestParsingTable

def testParser (rbp : Nat := 0) : Parser :=
{ fn := fun _ => runBuiltinParser "testExpr" builtinTestParsingTable rbp }

end Parser
end Lean
