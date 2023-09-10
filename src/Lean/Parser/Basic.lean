/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Parser.Types

/-!
# Basic Lean parser infrastructure

The Lean parser was developed with the following primary goals in mind:

* flexibility: Lean's grammar is complex and includes indentation and other whitespace sensitivity. It should be
  possible to introduce such custom "tweaks" locally without having to adjust the fundamental parsing approach.
* extensibility: Lean's grammar can be extended on the fly within a Lean file, and with Lean 4 we want to extend this
  to cover embedding domain-specific languages that may look nothing like Lean, down to using a separate set of tokens.
* losslessness: The parser should produce a concrete syntax tree that preserves all whitespace and other "sub-token"
  information for the use in tooling.
* performance: The overhead of the parser building blocks, and the overall parser performance on average-complexity
  input, should be comparable with that of the previous parser hand-written in C++. No fancy optimizations should be
  necessary for this.

Given these constraints, we decided to implement a combinatoric, non-monadic, lexer-less, memoizing recursive-descent
parser. Using combinators instead of some more formal and introspectible grammar representation ensures ultimate
flexibility as well as efficient extensibility: there is (almost) no pre-processing necessary when extending the grammar
with a new parser. However, because all the results the combinators produce are of the homogeneous `Syntax` type, the
basic parser type is not actually a monad but a monomorphic linear function `ParserState → ParserState`, avoiding
constructing and deconstructing countless monadic return values. Instead of explicitly returning syntax objects, parsers
push (zero or more of) them onto a syntax stack inside the linear state. Chaining parsers via `>>` accumulates their
output on the stack. Combinators such as `node` then pop off all syntax objects produced during their invocation and
wrap them in a single `Syntax.node` object that is again pushed on this stack. Instead of calling `node` directly, we
usually use the macro `leading_parser p`, which unfolds to `node k p` where the new syntax node kind `k` is the name of the
declaration being defined.

The lack of a dedicated lexer ensures we can modify and replace the lexical grammar at any point, and simplifies
detecting and propagating whitespace. The parser still has a concept of "tokens", however, and caches the most recent
one for performance: when `tokenFn` is called twice at the same position in the input, it will reuse the result of the
first call. `tokenFn` recognizes some built-in variable-length tokens such as identifiers as well as any fixed token in
the `ParserContext`'s `TokenTable` (a trie); however, the same cache field and strategy could be reused by custom token
parsers. Tokens also play a central role in the `prattParser` combinator, which selects a *leading* parser followed by
zero or more *trailing* parsers based on the current token (via `peekToken`); see the documentation of `prattParser`
for more details. Tokens are specified via the `symbol` parser, or with `symbolNoWs` for tokens that should not be preceded by whitespace.

The `Parser` type is extended with additional metadata over the mere parsing function to propagate token information:
`collectTokens` collects all tokens within a parser for registering. `firstTokens` holds information about the "FIRST"
token set used to speed up parser selection in `prattParser`. This approach of combining static and dynamic information
in the parser type is inspired by the paper "Deterministic, Error-Correcting Combinator Parsers" by Swierstra and Duponcheel.
If multiple parsers accept the same current token, `prattParser` tries all of them using the backtracking `longestMatchFn` combinator.
This is the only case where standard parsers might execute arbitrary backtracking. Repeated invocations of the same category or concrete
parser at the same position are cached where possible; see `withCache`.

Finally, error reporting follows the standard combinatoric approach of collecting a single unexpected token/... and zero
or more expected tokens (see `Error` below). Expected tokens are e.g. set by `symbol` and merged by `<|>`. Combinators
running multiple parsers should check if an error message is set in the parser state (`hasError`) and act accordingly.
Error recovery is left to the designer of the specific language; for example, Lean's top-level `parseCommand` loop skips
tokens until the next command keyword on error.
-/

namespace Lean.Parser

def dbgTraceStateFn (label : String) (p : ParserFn) : ParserFn :=
  fun c s =>
    let sz := s.stxStack.size
    let s' := p c s
    dbg_trace "{label}
  pos: {s'.pos}
  err: {s'.errorMsg}
  out: {s'.stxStack.extract sz s'.stxStack.size}"
    s'

def dbgTraceState (label : String) : Parser → Parser := withFn (dbgTraceStateFn label)

@[noinline]def epsilonInfo : ParserInfo :=
  { firstTokens := FirstTokens.epsilon }

def checkStackTopFn (p : Syntax → Bool) (msg : String) : ParserFn := fun _ s =>
  if p s.stxStack.back then s
  else s.mkUnexpectedError msg

def checkStackTop (p : Syntax → Bool) (msg : String) : Parser := {
  info := epsilonInfo,
  fn   := checkStackTopFn p msg
}

def andthenTokenFn (p q : TokenParserFn) : TokenParserFn := fun c s =>
  let s := p c s
  if s.hasError then s else q c s

def andthenFn (p q : ParserFn) : ParserFn := fun c s =>
  let s := p c s
  if s.hasError then s else q c s

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.seq q.firstTokens
}

/-- The `andthen(p, q)` combinator, usually written as adjacency in syntax declarations (`p q`),
parses `p` followed by `q`.

The arity of this parser is the sum of the arities of `p` and `q`:
that is, it accumulates all the nodes produced by `p` followed by the nodes from `q` into the list
of arguments to the surrounding parse node. -/
def andthen (p q : Parser) : Parser where
  info := andthenInfo p.info q.info
  fn   := andthenFn p.fn q.fn

instance : AndThen Parser where
  andThen a b := andthen a (b ())

def skipFn : TokenParserFn := fun _ s => s

def skip : Parser := {
  fn   := skipFn
  info := epsilonInfo
}

def nodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s     := p c s
  s.mkNode n iniSz

def trailingNodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s     := p c s
  s.mkTrailingNode n iniSz

@[noinline] def nodeInfo (n : SyntaxNodeKind) (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens,
  collectKinds  := fun s => (p.collectKinds s).insert n,
  firstTokens   := p.firstTokens
}

def node (n : SyntaxNodeKind) (p : Parser) : Parser := {
  info := nodeInfo n p.info,
  fn   := nodeFn n p.fn
}

def errorFn (msg : String) : ParserFn := fun _ s =>
  s.mkUnexpectedError msg

def error (msg : String) : Parser := {
  info := epsilonInfo,
  fn   := errorFn msg
}

def errorAtSavedPosFn (msg : String) (delta : Bool) : ParserFn := fun c s =>
  match c.savedPos? with
  | none     => s
  | some pos =>
    let pos := if delta then c.input.next pos else pos
    match s with
    | ⟨stack, lhsPrec, _, cache, _⟩ => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { unexpected := msg }⟩

/-- Generate an error at the position saved with the `withPosition` combinator.
   If `delta == true`, then it reports at saved position+1.
   This useful to make sure a parser consumed at least one character.  -/
def errorAtSavedPos (msg : String) (delta : Bool) : Parser := {
  fn := errorAtSavedPosFn msg delta
}

/-- Succeeds if `c.prec <= prec` -/
def checkPrecFn (prec : Nat) : ParserFn := fun c s =>
  if c.prec <= prec then s
  else s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"

def checkPrec (prec : Nat) : Parser := {
  info := epsilonInfo
  fn   := checkPrecFn prec
}

/-- Succeeds if `c.lhsPrec >= prec` -/
def checkLhsPrecFn (prec : Nat) : ParserFn := fun _ s =>
  if s.lhsPrec >= prec then s
  else s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"

def checkLhsPrec (prec : Nat) : Parser := {
  info := epsilonInfo
  fn   := checkLhsPrecFn prec
}

def setLhsPrecFn (prec : Nat) : ParserFn := fun _ s =>
  if s.hasError then s
  else { s with lhsPrec := prec }

def setLhsPrec (prec : Nat) : Parser := {
  info := epsilonInfo
  fn   := setLhsPrecFn prec
}

private def addQuotDepth (i : Int) (p : Parser) : Parser :=
  adaptCacheableContext (fun c => { c with quotDepth := c.quotDepth + i |>.toNat }) p

def incQuotDepth (p : Parser) : Parser := addQuotDepth 1 p

def decQuotDepth (p : Parser) : Parser := addQuotDepth (-1) p

def suppressInsideQuot : Parser → Parser :=
  adaptCacheableContext fun c =>
    -- if we are already within a quotation, don't change anything
    if c.quotDepth == 0 then { c with suppressInsideQuot := true } else c

def leadingNode (n : SyntaxNodeKind) (prec : Nat) (p : Parser) : Parser :=
  checkPrec prec >> node n p >> setLhsPrec prec

def trailingNodeAux (n : SyntaxNodeKind) (p : Parser) : TrailingParser := {
  info := nodeInfo n p.info
  fn   := trailingNodeFn n p.fn
}

def trailingNode (n : SyntaxNodeKind) (prec lhsPrec : Nat) (p : Parser) : TrailingParser :=
  checkPrec prec >> checkLhsPrec lhsPrec >> trailingNodeAux n p >> setLhsPrec prec

def mergeOrElseErrors (s : ParserState) (error1 : Error) (iniPos : String.Pos) (mergeErrors : Bool) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, some error2⟩ =>
    if pos == iniPos then ⟨stack, lhsPrec, pos, cache, some (if mergeErrors then error1.merge error2 else error2)⟩
    else s
  | other => other

-- When `p` in `p <|> q` parses exactly one antiquotation, ...
inductive OrElseOnAntiquotBehavior where
  | acceptLhs    -- return it
  | takeLongest  -- return result of `q` instead if it made more progress
  | merge        -- ... and create choice node if both made the same progress
  deriving BEq

def orelseFnCore (p q : ParserFn) (antiquotBehavior := OrElseOnAntiquotBehavior.merge) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let mut s  := p c s
  match s.errorMsg with
  | some errorMsg =>
    if s.pos == iniPos then
      mergeOrElseErrors (q c (s.restore iniSz iniPos)) errorMsg iniPos true
    else
      s
  | none =>
    let pBack := s.stxStack.back
    if antiquotBehavior == .acceptLhs || s.stackSize != iniSz + 1 || !pBack.isAntiquots then
      return s
    let pPos := s.pos
    s := s.restore iniSz iniPos
    s := q c s
    if s.hasError then
      return s.restore iniSz pPos |>.pushSyntax pBack
    -- If `q` made more progress than `p`, we prefer its result.
    -- Thus `(structInstField| $id := $val) is interpreted as
    -- `(structInstField| $id:ident := $val:term), not
    -- `(structInstField| $id:structInstField <ERROR: expected ')'>.
    if s.pos > pPos then
      return s
    if s.pos < pPos || antiquotBehavior != .merge || s.stackSize != iniSz + 1 || !s.stxStack.back.isAntiquots then
      return s.restore iniSz pPos |>.pushSyntax pBack
    -- Pop off result of `q`, push result(s) of `p` and `q` in that order, turn them into a choice node
    let qBack := s.stxStack.back
    s := s.popSyntax
    let pushAntiquots stx s :=
      if stx.isOfKind choiceKind then
        -- Flatten existing choice node
        { s with stxStack := s.stxStack ++ stx.getArgs }
      else
        s.pushSyntax stx
    s := pushAntiquots pBack s
    s := pushAntiquots qBack s
    s.mkNode choiceKind iniSz

def orelseFn (p q : ParserFn) : ParserFn :=
  orelseFnCore p q

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ q.collectTokens
  collectKinds  := p.collectKinds ∘ q.collectKinds
  firstTokens   := p.firstTokens.merge q.firstTokens
}

/--
  Run `p`, falling back to `q` if `p` failed without consuming any input.

  NOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser
  producing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`
  is fine as well. -/
def orelse (p q : Parser) : Parser where
  info := orelseInfo p.info q.info
  fn   := orelseFn p.fn q.fn

instance : OrElse Parser where
  orElse a b := orelse a (b ())

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo := {
  collectTokens := info.collectTokens
  collectKinds  := info.collectKinds
}

def atomicFn (p : ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  match p c s with
  | ⟨stack, lhsPrec, _, cache, some msg⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg⟩
  | other                       => other

/-- The `atomic(p)` parser parses `p`, returns the same result as `p` and fails iff `p` fails,
but if `p` fails after consuming some tokens `atomic(p)` will fail without consuming tokens.
This is important for the `p <|> q` combinator, because it is not backtracking, and will fail if
`p` fails after consuming some tokens. To get backtracking behavior, use `atomic(p) <|> q` instead.

This parser has the same arity as `p` - it produces the same result as `p`. -/
def atomic : Parser → Parser := withFn atomicFn

def optionalFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s
  s.mkNode nullKind iniSz

@[noinline] def optionaInfo (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens
  collectKinds  := p.collectKinds
  firstTokens   := p.firstTokens.toOptional
}

def optionalNoAntiquot (p : Parser) : Parser := {
  info := optionaInfo p.info
  fn   := optionalFn p.fn
}

def lookaheadFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  if s.hasError then s else s.restore iniSz iniPos

/-- `lookahead(p)` runs `p` and fails if `p` does, but it produces no parse nodes and rewinds the
position to the original state on success. So for example `lookahead("=>")` will ensure that the
next token is `"=>"`, without actually consuming this token.

This parser has arity 0 - it does not capture anything. -/
def lookahead : Parser → Parser := withFn lookaheadFn

def notFollowedByFn (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  if s.hasError then
    s.restore iniSz iniPos
  else
    let s := s.restore iniSz iniPos
    s.mkUnexpectedError s!"unexpected {msg}"

/-- `notFollowedBy(p, "foo")` succeeds iff `p` fails;
if `p` succeeds then it fails with the message `"unexpected foo"`.

This parser has arity 0 - it does not capture anything. -/
def notFollowedBy (p : Parser) (msg : String) : Parser where
  fn := notFollowedByFn p.fn msg

partial def manyAux (p : ParserFn) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let mut s  := p c s
  if s.hasError then
    return if iniPos == s.pos then s.restore iniSz iniPos else s
  if iniPos == s.pos then
    return s.mkUnexpectedError "invalid 'many' parser combinator application, parser did not consume anything"
  if s.stackSize > iniSz + 1 then
    s := s.mkNode nullKind iniSz
  manyAux p c s

def manyFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := manyAux p c s
  s.mkNode nullKind iniSz

def manyNoAntiquot (p : Parser) : Parser := {
  info := noFirstTokenInfo p.info
  fn   := manyFn p.fn
}

def many1Fn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := andthenFn p (manyAux p) c s
  s.mkNode nullKind iniSz

def many1NoAntiquot : Parser → Parser := withFn many1Fn

private partial def sepByFnAux (p : ParserFn) (sep : ParserFn) (allowTrailingSep : Bool) (iniSz : Nat) (pOpt : Bool) : ParserFn :=
  let rec parse (pOpt : Bool) (c s) := Id.run do
    let sz  := s.stackSize
    let pos := s.pos
    let mut s := p c s
    if s.hasError then
      if s.pos > pos then
        return s.mkNode nullKind iniSz
      else if pOpt then
        s := s.restore sz pos
        return s.mkNode nullKind iniSz
      else
        -- append `Syntax.missing` to make clear that List is incomplete
        s := s.pushSyntax Syntax.missing
        return s.mkNode nullKind iniSz
    if s.stackSize > sz + 1 then
      s := s.mkNode nullKind sz
    let sz  := s.stackSize
    let pos := s.pos
    s := sep c s
    if s.hasError then
      s := s.restore sz pos
      return s.mkNode nullKind iniSz
    if s.stackSize > sz + 1 then
      s := s.mkNode nullKind sz
    parse allowTrailingSep c s
  parse pOpt

def sepByFn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  sepByFnAux p sep allowTrailingSep iniSz true c s

def sepBy1Fn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  sepByFnAux p sep allowTrailingSep iniSz false c s

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ sep.collectTokens
  collectKinds  := p.collectKinds ∘ sep.collectKinds
}

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ sep.collectTokens
  collectKinds  := p.collectKinds ∘ sep.collectKinds
  firstTokens   := p.firstTokens
}

def sepByNoAntiquot (p sep : Parser) (allowTrailingSep : Bool := false) : Parser := {
  info := sepByInfo p.info sep.info
  fn   := sepByFn allowTrailingSep p.fn sep.fn
}

def sepBy1NoAntiquot (p sep : Parser) (allowTrailingSep : Bool := false) : Parser := {
  info := sepBy1Info p.info sep.info
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn
}

/-- Apply `f` to the syntax object produced by `p` -/
def withResultOfFn (p : ParserFn) (f : Syntax → Syntax) : ParserFn := fun c s =>
  let s := p c s
  if s.hasError then s
  else
    let stx := s.stxStack.back
    s.popSyntax.pushSyntax (f stx)

@[noinline] def withResultOfInfo (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens
  collectKinds  := p.collectKinds
}

def withResultOf (p : Parser) (f : Syntax → Syntax) : Parser := {
  info := withResultOfInfo p.info
  fn   := withResultOfFn p.fn f
}

def many1Unbox (p : Parser) : Parser :=
  withResultOf (many1NoAntiquot p) fun stx => if stx.getNumArgs == 1 then stx.getArg 0 else stx

partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : TokenParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s.mkEOIError
  else if p (c.input.get' i h) then s.next' c.input i h
  else s.mkUnexpectedError errorMsg

partial def takeUntilFn (p : Char → Bool) : TokenParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then s
  else if p (c.input.get' i h) then s
  else takeUntilFn p c (s.next' c.input i h)

def takeWhileFn (p : Char → Bool) : TokenParserFn :=
  takeUntilFn (fun c => !p c)

def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : TokenParserFn :=
  andthenTokenFn (satisfyFn p errorMsg) (takeWhileFn p)

def mkEmptySubstringAt (s : String) (p : String.Pos) : Substring := {
  str := s, startPos := p, stopPos := p
}

/-- Function to be called directly after parsing a token. When not in an error state, parses following whitespace,
    sets up `SourceInfo`, and pushes result of calling `f` with token substring and info onto stack. -/
@[specialize]
def pushToken (f : Substring → SourceInfo → Syntax) (startPos : String.Pos) (whitespaceFn : TokenParserFn) :
    TokenParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let input     := c.input
  let stopPos   := s.pos
  let leading   := mkEmptySubstringAt input startPos
  let rawVal    := { str := input, startPos := startPos, stopPos := stopPos  : Substring }
  let s         := whitespaceFn c s
  let wsStopPos := s.pos
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (f rawVal info)

/-- Push `(Syntax.node tk <new-atom>)` onto syntax stack if parse was successful. -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : String.Pos) (whitespaceFn : TokenParserFn) : TokenParserFn :=
  pushToken (fun ss info => .mkLit n ss.toString info) startPos whitespaceFn

/-- Match an arbitrary parser and return the consumed String in a `Syntax.atom`. -/
def rawFn (p : ParserFn) (whitespaceFn : TokenParserFn) : ParserFn := fun c s => Id.run do
  let startPos := s.pos
  let s := p c s
  if s.hasError then
    return s
  pushToken (fun ss info => .atom info ss.toString) startPos whitespaceFn c.toTokenParserContext s

def chFn (c : Char) (whitespaceFn : TokenParserFn) : ParserFn :=
  rawFn (satisfyFn (fun d => c == d) ("'" ++ toString c ++ "'")) whitespaceFn

def rawCh (c : Char) (whitespaceFn : TokenParserFn) : Parser := {
  fn := chFn c whitespaceFn
}

private def updateTokenCache (startPos : String.Pos) (s : ParserState) : ParserState :=
  -- do not cache token parsing errors, which are rare and usually fatal and thus not worth an extra field in `TokenCache`
  match s with
  | ⟨stack, lhsPrec, pos, ⟨_, catCache⟩, none⟩ =>
    if stack.size == 0 then s
    else
      let tk := stack.back
      ⟨stack, lhsPrec, pos, ⟨{ startPos := startPos, stopPos := pos, token := tk }, catCache⟩, none⟩
  | other => other

def tokenFn (expected : List String := []) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError expected
  else
    let tkc := s.cache.tokenCache
    if tkc.startPos == i then
      let s := s.pushSyntax tkc.token
      s.setPos tkc.stopPos
    else
      let s := c.tokenFn c.toTokenParserContext s
      updateTokenCache i s

def peekTokenAux (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn [] c s
  if let some _ := s.errorMsg then (s.restore iniSz iniPos, .error s)
  else
    let stx := s.stxStack.back
    (s.restore iniSz iniPos, .ok stx)

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let tkc := s.cache.tokenCache
  if tkc.startPos == s.pos then
    (s, .ok tkc.token)
  else
    peekTokenAux c s

def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let startPos := s.pos
  let s        := tokenFn expected c s
  if s.hasError then
    s
  else
    match s.stxStack.back with
    | .atom _ sym => if p sym then s else s.mkErrorsAt expected startPos initStackSz
    | _           => s.mkErrorsAt expected startPos initStackSz

def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolInfo (sym : String) : ParserInfo := {
  collectTokens := fun tks => sym :: tks
  firstTokens   := FirstTokens.tokens [ sym ]
}

def symbolFn (sym : String) : ParserFn :=
  symbolFnAux sym ("'" ++ sym ++ "'")

def symbolNoAntiquot (sym : String) : Parser :=
  let sym := sym.trim
  { info := symbolInfo sym
    fn   := symbolFn sym }

def checkTailNoWs (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | .original _ _ trailing _ => trailing.stopPos == trailing.startPos
  | _                        => false

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` Function is parsed using this combinator so that
    it can still be used as an identifier outside of universe (but registering it
    as a token in a Term Syntax would not break the universe Parser). -/
def nonReservedSymbolFnAux (sym : String) (errorMsg : String) : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let startPos := s.pos
  let s := tokenFn [errorMsg] c s
  if s.hasError then s
  else
    match s.stxStack.back with
    | .atom _ sym' =>
      if sym == sym' then s else s.mkErrorAt errorMsg startPos initStackSz
    | .ident info rawVal _ _ =>
      if sym == rawVal.toString then
        let s := s.popSyntax
        s.pushSyntax (Syntax.atom info sym)
      else
        s.mkErrorAt errorMsg startPos initStackSz
    | _ => s.mkErrorAt errorMsg startPos initStackSz

def nonReservedSymbolFn (sym : String) : ParserFn :=
  nonReservedSymbolFnAux sym ("'" ++ sym ++ "'")

def nonReservedSymbolInfo (sym : String) (includeIdent : Bool) : ParserInfo := {
  firstTokens  :=
    if includeIdent then
      .tokens [ sym, "ident" ]
    else
      .tokens [ sym ]
}

def nonReservedSymbolNoAntiquot (sym : String) (includeIdent := false) : Parser :=
  let sym := sym.trim
  { info := nonReservedSymbolInfo sym includeIdent,
    fn   := nonReservedSymbolFn sym }

partial def strAux (sym : String) (errorMsg : String) (j : String.Pos) :ParserFn :=
  let rec parse (j c s) :=
    if h₁ : sym.atEnd j then s
    else
      let i := s.pos
      let input := c.input
      if h₂ : input.atEnd i then s.mkError errorMsg
      else if sym.get' j h₁ != input.get' i h₂ then s.mkError errorMsg
      else parse (sym.next' j h₁) c (s.next' input i h₂)
  parse j

def checkTailWs (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | .original _ _ trailing _ => trailing.stopPos > trailing.startPos
  | _                        => false

def checkWsBeforeFn (errorMsg : String) : ParserFn := fun _ s =>
  let prev := s.stxStack.back
  if checkTailWs prev then s else s.mkError errorMsg

/-- The `ws` parser requires that there is some whitespace at this location.
For example, the parser `"foo" ws "+"` parses `foo +` or `foo/- -/+` but not `foo+`.

This parser has arity 0 - it does not capture anything. -/
def checkWsBefore (errorMsg : String := "space before") : Parser where
  info := epsilonInfo
  fn   := checkWsBeforeFn errorMsg

def checkTailLinebreak (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | .original _ _ trailing _ => trailing.contains '\n'
  | _ => false

def checkLinebreakBeforeFn (errorMsg : String) : ParserFn := fun _ s =>
  let prev := s.stxStack.back
  if checkTailLinebreak prev then s else s.mkError errorMsg

/-- The `linebreak` parser requires that there is at least one line break at this location.
(The line break may be inside a comment.)

This parser has arity 0 - it does not capture anything. -/
def checkLinebreakBefore (errorMsg : String := "line break") : Parser where
  info := epsilonInfo
  fn   := checkLinebreakBeforeFn errorMsg

private def pickNonNone (stack : SyntaxStack) : Syntax :=
  match stack.toSubarray.findRev? fun stx => !stx.isNone with
  | none => Syntax.missing
  | some stx => stx

def checkNoWsBeforeFn (errorMsg : String) : ParserFn := fun _ s =>
  let prev := pickNonNone s.stxStack
  if checkTailNoWs prev then s else s.mkError errorMsg

/-- The `noWs` parser requires that there is *no* whitespace between the preceding and following
parsers. For example, the parser `"foo" noWs "+"` parses `foo+` but not `foo +`.

This is almost the same as `"foo+"`, but using this parser will make `foo+` a token, which may cause
problems for the use of `"foo"` and `"+"` as separate tokens in other parsers.

This parser has arity 0 - it does not capture anything. -/
def checkNoWsBefore (errorMsg : String := "no space before") : Parser := {
  info := epsilonInfo
  fn   := checkNoWsBeforeFn errorMsg
}

def unicodeSymbolFnAux (sym asciiSym : String) (expected : List String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym || s == asciiSym) expected

def unicodeSymbolInfo (sym asciiSym : String) : ParserInfo := {
  collectTokens := fun tks => sym :: asciiSym :: tks
  firstTokens   := FirstTokens.tokens [ sym, asciiSym ]
}

def unicodeSymbolFn (sym asciiSym : String) : ParserFn :=
  unicodeSymbolFnAux sym asciiSym ["'" ++ sym ++ "', '" ++ asciiSym ++ "'"]

def unicodeSymbolNoAntiquot (sym asciiSym : String) : Parser :=
  let sym := sym.trim
  let asciiSym := asciiSym.trim
  { info := unicodeSymbolInfo sym asciiSym
    fn   := unicodeSymbolFn sym asciiSym }

def mkAtomicInfo (k : String) : ParserInfo :=
  { firstTokens := FirstTokens.tokens [ k ] }

def numLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["numeral"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind numLitKind) then s.mkErrorAt "numeral" iniPos initStackSz else s

def numLitNoAntiquot : Parser := {
  fn   := numLitFn
  info := mkAtomicInfo "num"
}

def scientificLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["scientific number"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind scientificLitKind) then s.mkErrorAt "scientific number" iniPos initStackSz else s

def scientificLitNoAntiquot : Parser := {
  fn   := scientificLitFn
  info := mkAtomicInfo "scientific"
}

def strLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["string literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "string literal" iniPos initStackSz else s

def strLitNoAntiquot : Parser := {
  fn   := strLitFn
  info := mkAtomicInfo "str"
}

def charLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["char literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind charLitKind) then s.mkErrorAt "character literal" iniPos initStackSz else s

def charLitNoAntiquot : Parser := {
  fn   := charLitFn
  info := mkAtomicInfo "char"
}

def nameLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["Name literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind nameLitKind) then s.mkErrorAt "Name literal" iniPos initStackSz else s

def nameLitNoAntiquot : Parser := {
  fn   := nameLitFn
  info := mkAtomicInfo "name"
}

def identFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["identifier"] c s
  if !s.hasError && !(s.stxStack.back.isIdent) then s.mkErrorAt "identifier" iniPos initStackSz else s

def identNoAntiquot : Parser := {
  fn   := identFn
  info := mkAtomicInfo "ident"
}

def identEqFn (id : Name) : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["identifier"] c s
  if s.hasError then
    s
  else match s.stxStack.back with
    | .ident _ _ val _ => if val != id then s.mkErrorAt ("expected identifier '" ++ toString id ++ "'") iniPos initStackSz else s
    | _ => s.mkErrorAt "identifier" iniPos initStackSz

def identEq (id : Name) : Parser := {
  fn   := identEqFn id
  info := mkAtomicInfo "ident"
}

def hygieneInfoFn : ParserFn := fun c s => Id.run do
  let input := c.input
  let finish pos str trailing s :=
    -- Builds an actual hygieneInfo node from empty string `str` and trailing whitespace `trailing`.
    let info  := SourceInfo.original str pos trailing pos
    let ident := mkIdent info str .anonymous
    let stx   := mkNode hygieneInfoKind #[ident]
    s.pushSyntax stx
  -- If we are at the whitespace after a token, the last item on the stack
  -- will have trailing whitespace. We want to position this hygieneInfo
  -- item immediately after the last token, and reattribute the trailing whitespace
  -- to the hygieneInfo node itself. This allows combinators like `ws` to
  -- be unaffected by `hygieneInfo` parsers before or after, see `2262.lean`.
  if !s.stxStack.isEmpty then
    let prev := s.stxStack.back
    if let .original leading pos trailing endPos := prev.getTailInfo then
      let str := mkEmptySubstringAt input endPos
      -- steal the trailing whitespace from the last node and use it for this node
      let s := s.popSyntax.pushSyntax <| prev.setTailInfo (.original leading pos str endPos)
      return finish endPos str trailing s
  -- The stack can be empty if this is either the first token, or if we are in a fresh cache.
  -- In that case we just put the hygieneInfo at the current location.
  let str := mkEmptySubstringAt input s.pos
  finish s.pos str str s

def hygieneInfoNoAntiquot : Parser := {
  fn   := hygieneInfoFn
  info := nodeInfo hygieneInfoKind epsilonInfo
}

namespace ParserState

def keepTop (s : SyntaxStack) (startStackSize : Nat) : SyntaxStack :=
  let node  := s.back
  s.shrink startStackSize |>.push node

def keepNewError (s : ParserState) (oldStackSize : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ => ⟨keepTop stack oldStackSize, lhsPrec, pos, cache, err⟩

def keepPrevError (s : ParserState) (oldStackSize : Nat) (oldStopPos : String.Pos) (oldError : Option Error) (oldLhsPrec : Nat) : ParserState :=
  match s with
  | ⟨stack, _, _, cache, _⟩ => ⟨stack.shrink oldStackSize, oldLhsPrec, oldStopPos, cache, oldError⟩

def mergeErrors (s : ParserState) (oldStackSize : Nat) (oldError : Error) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, some err⟩ =>
    ⟨stack.shrink oldStackSize, lhsPrec, pos, cache, if oldError == err then some err else some (oldError.merge err)⟩
  | other                         => other

def keepLatest (s : ParserState) (startStackSize : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ => ⟨keepTop stack startStackSize, lhsPrec, pos, cache, none⟩

def replaceLongest (s : ParserState) (startStackSize : Nat) : ParserState :=
  s.keepLatest startStackSize

end ParserState

def invalidLongestMatchParser (s : ParserState) : ParserState :=
  s.mkError "longestMatch parsers must generate exactly one Syntax node"

/--
 Auxiliary function used to execute parsers provided to `longestMatchFn`.
 Push `left?` into the stack if it is not `none`, and execute `p`.

 Remark: `p` must produce exactly one syntax node.
 Remark: the `left?` is not none when we are processing trailing parsers. -/
def runLongestMatchParser (left? : Option Syntax) (startLhsPrec : Nat) (p : ParserFn) : ParserFn := fun c s => Id.run do
  /-
    We assume any registered parser `p` has one of two forms:
    * a direct call to `leadingParser` or `trailingParser`
    * a direct call to a (leading) token parser
    In the first case, we can extract the precedence of the parser by having `leadingParser/trailingParser`
    set `ParserState.lhsPrec` to it in the very end so that no nested parser can interfere.
    In the second case, the precedence is effectively `max` (there is a `checkPrec` merely for the convenience
    of the pretty printer) and there are no nested `leadingParser/trailingParser` calls, so the value of `lhsPrec`
    will not be changed by the parser (nor will it be read by any leading parser). Thus we initialize the field
    to `maxPrec` in the leading case. -/
  let mut s := { s with lhsPrec := if left?.isSome then startLhsPrec else maxPrec }
  let startSize := s.stackSize
  if let some left := left? then
    s := s.pushSyntax left
  s := p c s
  -- stack contains `[..., result ]`
  if s.stackSize == startSize + 1 then
    s -- success or error with the expected number of nodes
  else if s.hasError then
    -- error with an unexpected number of nodes.
    s.shrinkStack startSize |>.pushSyntax Syntax.missing
  else
    -- parser succeded with incorrect number of nodes
    invalidLongestMatchParser s

def longestMatchStep (left? : Option Syntax) (startSize startLhsPrec : Nat) (startPos : String.Pos) (prevPrio : Nat) (prio : Nat) (p : ParserFn)
    : ParserContext → ParserState → ParserState × Nat := fun c s =>
  let score (s : ParserState) (prio : Nat) :=
    (s.pos.byteIdx, if s.errorMsg.isSome then (0 : Nat) else 1, prio)
  let previousScore := score s prevPrio
  let prevErrorMsg  := s.errorMsg
  let prevStopPos   := s.pos
  let prevSize      := s.stackSize
  let prevLhsPrec   := s.lhsPrec
  let s             := s.restore prevSize startPos
  let s             := runLongestMatchParser left? startLhsPrec p c s
  match (let _ := @lexOrd; compare previousScore (score s prio)) with
  | .lt => (s.keepNewError startSize, prio)
  | .gt => (s.keepPrevError prevSize prevStopPos prevErrorMsg prevLhsPrec, prevPrio)
  | .eq =>
    match prevErrorMsg with
    | none =>
      -- it is not clear what the precedence of a choice node should be, so we conservatively take the minimum
      ({s with lhsPrec := s.lhsPrec.min prevLhsPrec }, prio)
    | some oldError => (s.mergeErrors prevSize oldError, prio)

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
  if s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux (left? : Option Syntax) (startSize startLhsPrec : Nat) (startPos : String.Pos) (prevPrio : Nat) (ps : List (Parser × Nat)) : ParserFn :=
  let rec parse (prevPrio : Nat) (ps : List (Parser × Nat)) :=
    match ps with
    | []    => fun _ s => longestMatchMkResult startSize s
    | p::ps => fun c s =>
      let (s, prevPrio) := longestMatchStep left? startSize startLhsPrec startPos prevPrio p.2 p.1.fn c s
      parse prevPrio ps c s
  parse prevPrio ps

def longestMatchFn (left? : Option Syntax) : List (Parser × Nat) → ParserFn
  | []    => fun _ s => s.mkError "longestMatch: empty list"
  | [p]   => fun c s => runLongestMatchParser left? s.lhsPrec p.1.fn c s
  | p::ps => fun c s =>
    let startSize := s.stackSize
    let startLhsPrec := s.lhsPrec
    let startPos  := s.pos
    let s         := runLongestMatchParser left? s.lhsPrec p.1.fn c s
    longestMatchFnAux left? startSize startLhsPrec startPos p.2 ps c s

def anyOfFn : List Parser → ParserFn
  | [],    _, s => s.mkError "anyOf: empty list"
  | [p],   c, s => p.fn c s
  | p::ps, c, s => orelseFn p.fn (anyOfFn ps) c s

def checkColEqFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.column = savedPos.column then s
    else s.mkError errorMsg

/-- The `colEq` parser ensures that the next token starts at exactly the column of the saved
position (see `withPosition`). This can be used to do whitespace sensitive syntax like
a `by` block or `do` block, where all the lines have to line up.

This parser has arity 0 - it does not capture anything. -/
def checkColEq (errorMsg : String := "checkColEq") : Parser where
  fn := checkColEqFn errorMsg

def checkColGeFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.column ≥ savedPos.column then s
    else s.mkError errorMsg

/-- The `colGe` parser requires that the next token starts from at least the column of the saved
position (see `withPosition`), but allows it to be more indented.
This can be used for whitespace sensitive syntax to ensure that a block does not go outside a
certain indentation scope. For example it is used in the lean grammar for `else if`, to ensure
that the `else` is not less indented than the `if` it matches with.

This parser has arity 0 - it does not capture anything. -/
def checkColGe (errorMsg : String := "checkColGe") : Parser where
  fn := checkColGeFn errorMsg

def checkColGtFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.column > savedPos.column then s
    else s.mkError errorMsg

/-- The `colGt` parser requires that the next token starts a strictly greater column than the saved
position (see `withPosition`). This can be used for whitespace sensitive syntax for the arguments
to a tactic, to ensure that the following tactic is not interpreted as an argument.
```
example (x : False) : False := by
  revert x
  exact id
```
Here, the `revert` tactic is followed by a list of `colGt ident`, because otherwise it would
interpret `exact` as an identifier and try to revert a variable named `exact`.

This parser has arity 0 - it does not capture anything. -/
def checkColGt (errorMsg : String := "checkColGt") : Parser where
  fn := checkColGtFn errorMsg

def checkLineEqFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.line == savedPos.line then s
    else s.mkError errorMsg

/-- The `lineEq` parser requires that the current token is on the same line as the saved position
(see `withPosition`). This can be used to ensure that composite tokens are not "broken up" across
different lines. For example, `else if` is parsed using `lineEq` to ensure that the two tokens
are on the same line.

This parser has arity 0 - it does not capture anything. -/
def checkLineEq (errorMsg : String := "checkLineEq") : Parser where
  fn := checkLineEqFn errorMsg

/-- `withPosition(p)` runs `p` while setting the "saved position" to the current position.
This has no effect on its own, but various other parsers access this position to achieve some
composite effect:

* `colGt`, `colGe`, `colEq` compare the column of the saved position to the current position,
  used to implement Python-style indentation sensitive blocks
* `lineEq` ensures that the current position is still on the same line as the saved position,
  used to implement composite tokens

The saved position is only available in the read-only state, which is why this is a scoping parser:
after the `withPosition(..)` block the saved position will be restored to its original value.

This parser has the same arity as `p` - it just forwards the results of `p`. -/
def withPosition : Parser → Parser := withFn fun f c s =>
    adaptCacheableContextFn ({ · with savedPos? := s.pos }) f c s

def withPositionAfterLinebreak : Parser → Parser := withFn fun f c s =>
  let prev := s.stxStack.back
  adaptCacheableContextFn (fun c => if checkTailLinebreak prev then { c with savedPos? := s.pos } else c) f c s

/-- `withoutPosition(p)` runs `p` without the saved position, meaning that position-checking
parsers like `colGt` will have no effect. This is usually used by bracketing constructs like
`(...)` so that the user can locally override whitespace sensitivity.

This parser has the same arity as `p` - it just forwards the results of `p`. -/
def withoutPosition (p : Parser) : Parser :=
  adaptCacheableContext ({ · with savedPos? := none }) p

/-- `withForbidden tk p` runs `p` with `tk` as a "forbidden token". This means that if the token
appears anywhere in `p` (unless it is nested in `withoutForbidden`), parsing will immediately
stop there, making `tk` effectively a lowest-precedence operator. This is used for parsers like
`for x in arr do ...`: `arr` is parsed as `withForbidden "do" term` because otherwise `arr do ...`
would be treated as an application.

This parser has the same arity as `p` - it just forwards the results of `p`. -/
def withForbidden (tk : Token) (p : Parser) : Parser :=
  adaptCacheableContext ({ · with forbiddenTk? := tk }) p

/-- `withoutForbidden(p)` runs `p` disabling the "forbidden token" (see `withForbidden`), if any.
This is usually used by bracketing constructs like `(...)` because there is no parsing ambiguity
inside these nested constructs.

This parser has the same arity as `p` - it just forwards the results of `p`. -/
def withoutForbidden (p : Parser) : Parser :=
  adaptCacheableContext ({ · with forbiddenTk? := none }) p

def eoiFn : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s
  else s.mkError "expected end of file"

def eoi : Parser := {
  fn := eoiFn
}

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickCmp

namespace TokenMap

def insert (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
  match map.find? k with
  | none    => .insert map k [v]
  | some vs => .insert map k (v::vs)

instance : Inhabited (TokenMap α) where
  default := RBMap.empty

instance : EmptyCollection (TokenMap α) := ⟨RBMap.empty⟩

instance : ForIn m (TokenMap α) (Name × List α) := inferInstanceAs (ForIn _ (RBMap ..) _)

end TokenMap

structure PrattParsingTables where
  leadingTable    : TokenMap (Parser × Nat) := {}
  leadingParsers  : List (Parser × Nat) := [] -- for supporting parsers we cannot obtain first token
  trailingTable   : TokenMap (Parser × Nat) := {}
  trailingParsers : List (Parser × Nat) := [] -- for supporting parsers such as function application

instance : Inhabited PrattParsingTables where
  default := {}

/--
  The type `LeadingIdentBehavior` specifies how the parsing table
  lookup function behaves for identifiers.  The function `prattParser`
  uses two tables `leadingTable` and `trailingTable`. They map tokens
  to parsers.

  We use `LeadingIdentBehavior.symbol` and `LeadingIdentBehavior.both`
  and `nonReservedSymbol` parser to implement the `tactic` parsers.
  The idea is to avoid creating a reserved symbol for each
  builtin tactic (e.g., `apply`, `assumption`, etc.).  That is, users
  may still use these symbols as identifiers (e.g., naming a
  function).
-/
inductive LeadingIdentBehavior where
  /-- `LeadingIdentBehavior.default`: if the leading token
  is an identifier, then `prattParser` just executes the parsers
  associated with the auxiliary token "ident". -/
  | default
  /-- `LeadingIdentBehavior.symbol`: if the leading token is
  an identifier `<foo>`, and there are parsers `P` associated with
  the token `<foo>`, then it executes `P`. Otherwise, it executes
  only the parsers associated with the auxiliary token "ident". -/
  | symbol
  /-- `LeadingIdentBehavior.both`: if the leading token
  an identifier `<foo>`, the it executes the parsers associated
  with token `<foo>` and parsers associated with the auxiliary
  token "ident". -/
  | both
  deriving Inhabited, BEq, Repr

/--
  Each parser category is implemented using a Pratt's parser.
  The system comes equipped with the following categories: `level`, `term`, `tactic`, and `command`.
  Users and plugins may define extra categories.

  The method
  ```
  categoryParser `term prec
  ```
  executes the Pratt's parser for category `term` with precedence `prec`.
  That is, only parsers with precedence at least `prec` are considered.
  The method `termParser prec` is equivalent to the method above.
-/
structure ParserCategory where
  /-- The name of a declaration which will be used as the target of
  go-to-definition queries and from which doc strings will be extracted.
  This is a dummy declaration of type `Lean.Parser.Category`
  created by `declare_syntax_cat`, but for builtin categories the declaration
  is made manually and passed to `registerBuiltinParserAttribute`. -/
  declName : Name
  /-- The list of syntax nodes that can parse into this category.
  This can be used to list all syntaxes in the category. -/
  kinds    : SyntaxNodeKindSet := {}
  /-- The parsing tables, which consist of a dynamic set of parser
  functions based on the syntaxes that have been declared so far. -/
  tables   : PrattParsingTables := {}
  /-- The `LeadingIdentBehavior`, which specifies how the parsing table
  lookup function behaves for the first identifier to be parsed.
  This is used by the `tactic` parser to avoid creating a reserved
  symbol for each builtin tactic (e.g., `apply`, `assumption`, etc.). -/
  behavior : LeadingIdentBehavior
  deriving Inhabited

abbrev ParserCategories := PersistentHashMap Name ParserCategory

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (behavior : LeadingIdentBehavior) : ParserState × List α :=
  let (s, stx) := peekToken c s
  let find (n : Name) : ParserState × List α :=
    match map.find? n with
    | some as => (s, as)
    | _       => (s, [])
  match stx with
  | .ok (.atom _ sym)      => find (.mkSimple sym)
  | .ok (.ident _ _ val _) =>
    match behavior with
    | .default => find identKind
    | .symbol =>
      match map.find? val with
      | some as => (s, as)
      | none    => find identKind
    | .both =>
      match map.find? val with
      | some as =>
        if val == identKind then
          (s, as)  -- avoid running the same parsers twice
        else
          match map.find? identKind with
          | some as' => (s, as ++ as')
          | _        => (s, as)
      | none    => find identKind
  | .ok (.node _ k _) => find k
  | .ok _             => (s, [])
  | .error s'         => (s', [])

abbrev CategoryParserFn := Name → ParserFn

builtin_initialize categoryParserFnRef : IO.Ref CategoryParserFn ← IO.mkRef fun (_ : Name) => skip.fn

builtin_initialize categoryParserFnExtension : EnvExtension CategoryParserFn ← registerEnvExtension $ categoryParserFnRef.get

def categoryParserFn (catName : Name) : ParserFn := fun ctx s =>
  categoryParserFnExtension.getState ctx.env catName ctx s

def categoryParser (catName : Name) (prec : Nat) : Parser where
  fn := adaptCacheableContextFn ({ · with prec }) (withCacheFn catName (categoryParserFn catName))

-- Define `termParser` here because we need it for antiquotations
def termParser (prec : Nat := 0) : Parser :=
  categoryParser `term prec

-- ==================
/-! # Antiquotations -/
-- ==================

/-- Fail if previous token is immediately followed by ':'. -/
def checkNoImmediateColon : Parser := {
  fn := fun c s =>
    let prev := s.stxStack.back
    if checkTailNoWs prev then
      let input := c.input
      let i     := s.pos
      if h : input.atEnd i then s
      else
        let curr := input.get' i h
        if curr == ':' then
          s.mkUnexpectedError "unexpected ':'"
        else s
    else s
}

def setExpectedFn (expected : List String) (p : ParserFn) : ParserFn := fun c s =>
  match p c s with
    | s'@{ errorMsg := some msg, .. } => { s' with errorMsg := some { msg with expected } }
    | s'                              => s'

def setExpected (expected : List String) : Parser → Parser := withFn (setExpectedFn expected)

def pushNone : Parser := {
  fn := fun _ s => s.pushSyntax mkNullNode
}

-- We support three kinds of antiquotations: `$id`, `$_`, and `$(t)`, where `id` is a term identifier and `t` is a term.
def antiquotNestedExpr : Parser := node `antiquotNestedExpr (symbolNoAntiquot "(" >> decQuotDepth termParser >> symbolNoAntiquot ")")
def antiquotExpr : Parser       := identNoAntiquot <|> symbolNoAntiquot "_" <|> antiquotNestedExpr

def tokenAntiquotFn : ParserFn := fun c s => Id.run do
  if s.hasError then
    return s
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := (checkNoWsBefore >> symbolNoAntiquot "%" >> symbolNoAntiquot "$" >> checkNoWsBefore >> antiquotExpr).fn c s
  if s.hasError then
    return s.restore iniSz iniPos
  s.mkNode (`token_antiquot) (iniSz - 1)

def tokenWithAntiquot : Parser → Parser := withFn fun f c s =>
  let s := f c s
  -- fast check that is false in most cases
  if c.input.get s.pos == '%' then
    tokenAntiquotFn c s
  else
    s

def symbol (sym : String) : Parser :=
  tokenWithAntiquot (symbolNoAntiquot sym)

instance : Coe String Parser where
  coe := symbol

def nonReservedSymbol (sym : String) (includeIdent := false) : Parser :=
  tokenWithAntiquot (nonReservedSymbolNoAntiquot sym includeIdent)

def unicodeSymbol (sym asciiSym : String) : Parser :=
  tokenWithAntiquot (unicodeSymbolNoAntiquot sym asciiSym)

/--
  Define parser for `$e` (if `anonymous == true`) and `$e:name`.
  `kind` is embedded in the antiquotation's kind, and checked at syntax `match` unless `isPseudoKind` is true.
  Antiquotations can be escaped as in `$$e`, which produces the syntax tree for `$e`. -/
def mkAntiquot (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Parser :=
  let kind := kind ++ (if isPseudoKind then `pseudo else .anonymous) ++ `antiquot
  let nameP := node `antiquotName <| checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbol ":" >> nonReservedSymbol name
  -- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
  -- antiquotation kind via `noImmediateColon`
  let nameP := if anonymous then nameP <|> checkNoImmediateColon >> pushNone else nameP
  -- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
  leadingNode kind maxPrec <| atomic <|
    setExpected [] "$" >>
    manyNoAntiquot (checkNoWsBefore "" >> "$") >>
    checkNoWsBefore "no space before spliced term" >> antiquotExpr >>
    nameP

def withAntiquotFn (antiquotP p : ParserFn) (isCatAntiquot := false) : ParserFn := fun c s =>
  -- fast check that is false in most cases
  if c.input.get s.pos == '$' then
    -- Do not allow antiquotation choice nodes here as `antiquotP` is the strictly more general
    -- antiquotation than any in `p`.
    -- If it is a category antiquotation, do not backtrack into the category at all as that would
    -- run *all* parsers of the category, and trailing parsers will later be applied anyway.
    orelseFnCore (antiquotBehavior := if isCatAntiquot then .acceptLhs else .takeLongest) antiquotP p c s
  else
    p c s

/-- Optimized version of `mkAntiquot ... <|> p`. -/
def withAntiquot (antiquotP p : Parser) : Parser := {
  fn := withAntiquotFn antiquotP.fn p.fn
  info := orelseInfo antiquotP.info p.info
}

def withoutInfo (p : Parser) : Parser := {
  fn := p.fn
}

/-- Parse `$[p]suffix`, e.g. `$[p],*`. -/
def mkAntiquotSplice (kind : SyntaxNodeKind) (p suffix : Parser) : Parser :=
  let kind := kind ++ `antiquot_scope
  leadingNode kind maxPrec <| atomic <|
    setExpected [] "$" >>
    manyNoAntiquot (checkNoWsBefore "" >> "$") >>
    checkNoWsBefore "no space before spliced term" >> symbol "[" >> node nullKind p >> symbol "]" >>
    suffix

private def withAntiquotSuffixSpliceFn (kind : SyntaxNodeKind) (suffix : ParserFn) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := suffix c s
  if s.hasError then
    return s.restore iniSz iniPos
  s.mkNode (kind ++ `antiquot_suffix_splice) (s.stxStack.size - 2)

/-- Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. -/
def withAntiquotSuffixSplice (kind : SyntaxNodeKind) (p suffix : Parser) : Parser where
  info := andthenInfo p.info suffix.info
  fn c s :=
    let s := p.fn c s
    -- fast check that is false in most cases
    if !s.hasError && s.stxStack.back.isAntiquots then
      withAntiquotSuffixSpliceFn kind suffix.fn c s
    else
      s

def withAntiquotSpliceAndSuffix (kind : SyntaxNodeKind) (p suffix : Parser) :=
  -- prevent `p`'s info from being collected twice
  withAntiquot (mkAntiquotSplice kind (withoutInfo p) suffix) (withAntiquotSuffixSplice kind p suffix)

def nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : Parser) (anonymous := false) : Parser :=
  withAntiquot (mkAntiquot name kind anonymous) $ node kind p

-- =========================
/-! # End of Antiquotations -/
-- =========================

def sepByElemParser (p : Parser) (sep : String) : Parser :=
  withAntiquotSpliceAndSuffix `sepBy p (symbol (sep.trim ++ "*"))

def sepBy (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepByNoAntiquot (sepByElemParser p sep) psep allowTrailingSep

def sepBy1 (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepBy1NoAntiquot (sepByElemParser p sep) psep allowTrailingSep

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
  if s.stackSize == iniSz + 1 then s
  else s.mkNode nullKind iniSz -- throw error instead?

def leadingParserAux (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) : ParserFn := fun c s => Id.run do
  let iniSz   := s.stackSize
  let (s, ps) := indexed tables.leadingTable c s behavior
  if s.hasError then
    return s
  let ps      := tables.leadingParsers ++ ps
  if ps.isEmpty then
    return s.mkError (toString kind)
  let s := longestMatchFn none ps c s
  mkResult s iniSz

def leadingParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn :=
  withAntiquotFn (isCatAntiquot := true) antiquotParser (leadingParserAux kind tables behavior)

def trailingLoopStep (tables : PrattParsingTables) (left : Syntax) (ps : List (Parser × Nat)) : ParserFn := fun c s =>
  longestMatchFn left (ps ++ tables.trailingParsers) c s

partial def trailingLoop (tables : PrattParsingTables) (c : ParserContext) (s : ParserState) : ParserState := Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let (s, ps)       := indexed tables.trailingTable c s LeadingIdentBehavior.default
  if s.hasError then
    -- Discard token parse errors and break the trailing loop instead.
    -- The error will be flagged when the next leading position is parsed, unless the token
    -- is in fact valid there (e.g. EOI at command level, no-longer forbidden token)
    return s.restore iniSz iniPos
  if ps.isEmpty && tables.trailingParsers.isEmpty then
    return s -- no available trailing parser
  let left   := s.stxStack.back
  let s      := s.popSyntax
  let s      := trailingLoopStep tables left ps c s
  if s.hasError then
    -- Discard non-consuming parse errors and break the trailing loop instead, restoring `left`.
    -- This is necessary for fallback parsers like `app` that pretend to be always applicable.
    return if s.pos == iniPos then s.restore (iniSz - 1) iniPos |>.pushSyntax left else s
  trailingLoop tables c s

/--

  Implements a variant of Pratt's algorithm. In Pratt's algorithms tokens have a right and left binding power.
  In our implementation, parsers have precedence instead. This method selects a parser (or more, via
  `longestMatchFn`) from `leadingTable` based on the current token. Note that the unindexed `leadingParsers` parsers
  are also tried. We have the unidexed `leadingParsers` because some parsers do not have a "first token". Example:
  ```
  syntax term:51 "≤" ident "<" term "|" term : index
  ```
  Example, in principle, the set of first tokens for this parser is any token that can start a term, but this set
  is always changing. Thus, this parsing rule is stored as an unindexed leading parser at `leadingParsers`.
  After processing the leading parser, we chain with parsers from `trailingTable`/`trailingParsers` that have precedence
  at least `c.prec` where `c` is the `ParsingContext`. Recall that `c.prec` is set by `categoryParser`.

  Note that in the original Pratt's algorith, precedences are only checked before calling trailing parsers. In our
  implementation, leading *and* trailing parsers check the precendece. We claim our algorithm is more flexible,
  modular and easier to understand.

  `antiquotParser` should be a `mkAntiquot` parser (or always fail) and is tried before all other parsers.
  It should not be added to the regular leading parsers because it would heavily
  overlap with antiquotation parsers nested inside them. -/
def prattParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn := fun c s =>
  let s := leadingParser kind tables behavior antiquotParser c s
  if s.hasError then
    s
  else
    trailingLoop tables c s

end Parser

namespace Syntax

section
variable [Monad m]

def foldArgsM (s : Syntax) (f : Syntax → β → m β) (b : β) : m β :=
  s.getArgs.foldlM (flip f) b

def foldArgs (s : Syntax) (f : Syntax → β → β) (b : β) : β :=
  Id.run (s.foldArgsM f b)

def forArgsM (s : Syntax) (f : Syntax → m Unit) : m Unit :=
  s.foldArgsM (fun s _ => f s) ()
end

end Syntax
end Lean
