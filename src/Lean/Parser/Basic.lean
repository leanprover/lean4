/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/

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
with a new parser. However, because the all results the combinators produce are of the homogeneous `Syntax` type, the
basic parser type is not actually a monad but a monomorphic linear function `ParserState → ParserState`, avoiding
constructing and deconstructing countless monadic return values. Instead of explicitly returning syntax objects, parsers
push (zero or more of) them onto a syntax stack inside the linear state. Chaining parsers via `>>` accumulates their
output on the stack. Combinators such as `node` then pop off all syntax objects produced during their invocation and
wrap them in a single `Syntax.node` object that is again pushed on this stack. Instead of calling `node` directly, we
usually use the macro `parser! p`, which unfolds to `node k p` where the new syntax node kind `k` is the name of the
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
This is the only case where standard parsers might execute arbitrary backtracking. At the moment there is no memoization shared by these
parallel parsers apart from the first token, though we might change this in the future if the need arises.

Finally, error reporting follows the standard combinatoric approach of collecting a single unexpected token/... and zero
or more expected tokens (see `Error` below). Expected tokens are e.g. set by `symbol` and merged by `<|>`. Combinators
running multiple parsers should check if an error message is set in the parser state (`hasError`) and act accordingly.
Error recovery is left to the designer of the specific language; for example, Lean's top-level `parseCommand` loop skips
tokens until the next command keyword on error.
-/
import Lean.Data.Trie
import Lean.Data.Position
import Lean.Syntax
import Lean.ToExpr
import Lean.Environment
import Lean.Attributes
import Lean.Message
import Lean.Compiler.InitAttr

namespace Lean

def quotedSymbolKind := `quotedSymbol

namespace Parser

def isLitKind (k : SyntaxNodeKind) : Bool :=
k == strLitKind || k == numLitKind || k == charLitKind || k == nameLitKind

abbrev mkAtom (info : SourceInfo) (val : String) : Syntax :=
Syntax.atom info val

abbrev mkIdent (info : SourceInfo) (rawVal : Substring) (val : Name) : Syntax :=
Syntax.ident info rawVal val []

/- Return character after position `pos` -/
def getNext (input : String) (pos : Nat) : Char :=
input.get (input.next pos)

/- Maximal (and function application) precedence.
   In the standard lean language, no parser has precedence higher than `maxPrec`.

   Note that nothing prevents users from using a higher precedence, but we strongly
   discourage them from doing it. -/
def maxPrec : Nat := 1024

abbrev Token := String

structure TokenCacheEntry :=
(startPos stopPos : String.Pos := 0)
(token : Syntax := Syntax.missing)

structure ParserCache :=
(tokenCache : TokenCacheEntry)

def initCacheForInput (input : String) : ParserCache :=
{ tokenCache := { startPos := input.bsize + 1 /- make sure it is not a valid position -/} }

abbrev TokenTable := Trie Token

abbrev SyntaxNodeKindSet := Std.PersistentHashMap SyntaxNodeKind Unit

def SyntaxNodeKindSet.insert (s : SyntaxNodeKindSet) (k : SyntaxNodeKind) : SyntaxNodeKindSet :=
s.insert k ()

/-
  Input string and related data. Recall that the `FileMap` is a helper structure for mapping
  `String.Pos` in the input string to line/column information.  -/
structure InputContext :=
(input    : String)
(fileName : String)
(fileMap  : FileMap)

instance InputContext.inhabited : Inhabited InputContext :=
⟨{ input := "", fileName := "", fileMap := arbitrary _ }⟩

structure ParserContext extends InputContext :=
(prec       : Nat)
(env        : Environment)
(tokens     : TokenTable)
(insideQuot : Bool := false)

structure Error :=
(unexpected : String := "")
(expected : List String := [])

namespace Error
instance : Inhabited Error := ⟨{}⟩

private def expectedToString : List String → String
| []       => ""
| [e]      => e
| [e1, e2] => e1 ++ " or " ++ e2
| e::es    => e ++ ", " ++ expectedToString es

protected def toString (e : Error) : String :=
let unexpected := if e.unexpected == "" then [] else [e.unexpected];
let expected   := if e.expected == [] then [] else
  let expected := e.expected.toArray.qsort (fun e e' => e < e');
  let expected := expected.toList.eraseReps;
  ["expected " ++ expectedToString expected];
"; ".intercalate $ unexpected ++ expected

instance : HasToString Error := ⟨Error.toString⟩

protected def beq (e₁ e₂ :  Error) : Bool :=
e₁.unexpected == e₂.unexpected && e₁.expected == e₂.expected

instance : HasBeq Error := ⟨Error.beq⟩

def merge (e₁ e₂ : Error) : Error :=
match e₂ with
| { unexpected := u, .. } => { unexpected := if u == "" then e₁.unexpected else u, expected := e₁.expected ++ e₂.expected }

end Error

structure ParserState :=
(stxStack : Array Syntax := #[])
(pos      : String.Pos := 0)
(cache    : ParserCache)
(errorMsg : Option Error := none)

namespace ParserState

@[inline] def hasError (s : ParserState) : Bool :=
s.errorMsg != none

@[inline] def stackSize (s : ParserState) : Nat :=
s.stxStack.size

def restore (s : ParserState) (iniStackSz : Nat) (iniPos : Nat) : ParserState :=
{ s with stxStack := s.stxStack.shrink iniStackSz, errorMsg := none, pos := iniPos }

def setPos (s : ParserState) (pos : Nat) : ParserState :=
{ s with pos := pos }

def setCache (s : ParserState) (cache : ParserCache) : ParserState :=
{ s with cache := cache }

def pushSyntax (s : ParserState) (n : Syntax) : ParserState :=
{ s with stxStack := s.stxStack.push n }

def popSyntax (s : ParserState) : ParserState :=
{ s with stxStack := s.stxStack.pop }

def shrinkStack (s : ParserState) (iniStackSz : Nat) : ParserState :=
{ s with stxStack := s.stxStack.shrink iniStackSz }

def next (s : ParserState) (input : String) (pos : Nat) : ParserState :=
{ s with pos := input.next pos }

def toErrorMsg (ctx : ParserContext) (s : ParserState) : String :=
match s.errorMsg with
| none     => ""
| some msg =>
  let pos := ctx.fileMap.toPosition s.pos;
  mkErrorStringWithPos ctx.fileName pos.line pos.column (toString msg)

def mkNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, err⟩ =>
  if err != none && stack.size == iniStackSz then
    -- If there is an error but there are no new nodes on the stack, we just return `s`
    s
  else
    let newNode := Syntax.node k (stack.extract iniStackSz stack.size);
    let stack   := stack.shrink iniStackSz;
    let stack   := stack.push newNode;
    ⟨stack, pos, cache, err⟩

def mkTrailingNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, err⟩ =>
  let newNode := Syntax.node k (stack.extract (iniStackSz - 1) stack.size);
  let stack   := stack.shrink iniStackSz;
  let stack   := stack.push newNode;
  ⟨stack, pos, cache, err⟩

def mkError (s : ParserState) (msg : String) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ => ⟨stack, pos, cache, some { expected := [ msg ] }⟩

def mkUnexpectedError (s : ParserState) (msg : String) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ => ⟨stack, pos, cache, some { unexpected := msg }⟩

def mkEOIError (s : ParserState) : ParserState :=
s.mkUnexpectedError "end of input"

def mkErrorAt (s : ParserState) (msg : String) (pos : String.Pos) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack, pos, cache, some { expected := [ msg ] }⟩

def mkErrorsAt (s : ParserState) (ex : List String) (pos : String.Pos) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack, pos, cache, some { expected := ex }⟩

def mkUnexpectedErrorAt (s : ParserState) (msg : String) (pos : String.Pos) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack, pos, cache, some { unexpected := msg }⟩

end ParserState

def ParserFn := ParserContext → ParserState → ParserState

instance ParserFn.inhabited : Inhabited ParserFn := ⟨fun _ => id⟩

inductive FirstTokens
| epsilon   : FirstTokens
| unknown   : FirstTokens
| tokens    : List Token → FirstTokens
| optTokens : List Token → FirstTokens

namespace FirstTokens

def seq : FirstTokens → FirstTokens → FirstTokens
| epsilon,      tks          => tks
| optTokens s₁, optTokens s₂ => optTokens (s₁ ++ s₂)
| optTokens s₁, tokens s₂    => tokens (s₁ ++ s₂)
| tks,          _            => tks

def toOptional : FirstTokens → FirstTokens
| tokens tks => optTokens tks
| tks        => tks

def merge : FirstTokens → FirstTokens → FirstTokens
| epsilon,      tks          => toOptional tks
| tks,          epsilon      => toOptional tks
| tokens s₁,    tokens s₂    => tokens (s₁ ++ s₂)
| optTokens s₁, optTokens s₂ => optTokens (s₁ ++ s₂)
| tokens s₁,    optTokens s₂ => optTokens (s₁ ++ s₂)
| optTokens s₁, tokens s₂    => optTokens (s₁ ++ s₂)
| _,            _            => unknown

def toStr : FirstTokens → String
| epsilon       => "epsilon"
| unknown       => "unknown"
| tokens tks    => toString tks
| optTokens tks => "?" ++ toString tks

instance : HasToString FirstTokens := ⟨toStr⟩

end FirstTokens

structure ParserInfo :=
(collectTokens : List Token → List Token := id)
(collectKinds  : SyntaxNodeKindSet → SyntaxNodeKindSet := id)
(firstTokens   : FirstTokens                           := FirstTokens.unknown)

structure Parser :=
(info : ParserInfo := {})
(fn   : ParserFn)

instance Parser.inhabited : Inhabited Parser :=
⟨{ fn := fun _ s => s }⟩

abbrev TrailingParser := Parser

@[noinline] def epsilonInfo : ParserInfo :=
{ firstTokens := FirstTokens.epsilon }

@[inline] def checkStackTopFn (p : Syntax → Bool) (msg : String) : ParserFn :=
fun c s =>
  if p s.stxStack.back then s
  else s.mkUnexpectedError msg

@[inline] def checkStackTop (p : Syntax → Bool) (msg : String) : Parser :=
{ info := epsilonInfo,
  fn   := checkStackTopFn p msg }

@[inline] def andthenFn (p q : ParserFn) : ParserFn :=
fun c s =>
  let s := p c s;
  if s.hasError then s else q c s

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.seq q.firstTokens }

@[inline] def andthen (p q : Parser) : Parser :=
{ info := andthenInfo p.info q.info,
  fn   := andthenFn p.fn q.fn }

instance hasAndthen : HasAndthen Parser :=
⟨andthen⟩

@[inline] def nodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  let s     := p c s;
  s.mkNode n iniSz

@[inline] def trailingNodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  let s     := p c s;
  s.mkTrailingNode n iniSz

@[noinline] def nodeInfo (n : SyntaxNodeKind) (p : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens,
  collectKinds  := fun s => (p.collectKinds s).insert n,
  firstTokens   := p.firstTokens }

@[inline] def node (n : SyntaxNodeKind) (p : Parser) : Parser :=
{ info := nodeInfo n p.info,
  fn   := nodeFn n p.fn }

/- Succeeds if `c.prec <= prec` -/
def checkPrecFn (prec : Nat) : ParserFn :=
fun c s =>
  if c.prec <= prec then s
  else s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def checkPrec (prec : Nat) : Parser :=
{ info := epsilonInfo,
  fn   := checkPrecFn prec }

def checkInsideQuotFn : ParserFn :=
fun c s =>
  if c.insideQuot then s
  else s.mkUnexpectedError "unexpected syntax outside syntax quotation"

@[inline] def checkInsideQuot : Parser :=
{ info := epsilonInfo,
  fn   := checkInsideQuotFn }

def checkOutsideQuotFn : ParserFn :=
fun c s =>
  if !c.insideQuot then s
  else s.mkUnexpectedError "unexpected syntax inside syntax quotation"

@[inline] def checkOutsideQuot : Parser :=
{ info := epsilonInfo,
  fn   := checkOutsideQuotFn }

def toggleInsideQuotFn (p : ParserFn) : ParserFn :=
fun c s => p { c with insideQuot := !c.insideQuot } s

@[inline] def toggleInsideQuot (p : Parser) : Parser :=
{ info := epsilonInfo,
  fn   := toggleInsideQuotFn p.fn }

@[inline] def leadingNode (n : SyntaxNodeKind) (prec : Nat) (p : Parser) : Parser :=
checkPrec prec >> node n p

@[inline] def trailingNodeAux (n : SyntaxNodeKind) (p : Parser) : TrailingParser :=
{ info := nodeInfo n p.info,
  fn   := trailingNodeFn n p.fn }

@[inline] def trailingNode (n : SyntaxNodeKind) (prec : Nat) (p : Parser) : TrailingParser :=
checkPrec prec >> trailingNodeAux n p

@[inline] def group (p : Parser) : Parser :=
node nullKind p

def mergeOrElseErrors (s : ParserState) (error1 : Error) (iniPos : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, some error2⟩ =>
  if pos == iniPos then ⟨stack, pos, cache, some (error1.merge error2)⟩
  else s
| other => other

@[inline] def orelseFn (p q : ParserFn) : ParserFn
| c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p c s;
  match s.errorMsg with
  | some errorMsg =>
    if s.pos == iniPos then
      mergeOrElseErrors (q c (s.restore iniSz iniPos)) errorMsg iniPos
    else
      s
  | none => s

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.merge q.firstTokens }

@[inline] def orelse (p q : Parser) : Parser :=
{ info := orelseInfo p.info q.info,
  fn   := orelseFn p.fn q.fn }

instance hashOrelse : HasOrelse Parser :=
⟨orelse⟩

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ collectTokens := info.collectTokens,
  collectKinds  := info.collectKinds }

@[inline] def tryFn (p : ParserFn) : ParserFn
| c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  match p c s with
  | ⟨stack, _, cache, some msg⟩ => ⟨stack.shrink iniSz, iniPos, cache, some msg⟩
  | other                       => other

@[inline] def try (p : Parser) : Parser :=
{ info := p.info,
  fn   := tryFn p.fn }

@[inline] def optionalFn (p : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p c s;
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s;
  s.mkNode nullKind iniSz

@[noinline] def optionaInfo (p : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens,
  collectKinds  := p.collectKinds,
  firstTokens   := p.firstTokens.toOptional }

@[inline] def optional (p : Parser) : Parser :=
{ info := optionaInfo p.info,
  fn   := optionalFn p.fn }

@[inline] def lookaheadFn (p : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p c s;
  if s.hasError then s else s.restore iniSz iniPos

@[inline] def lookahead (p : Parser) : Parser :=
{ info := p.info,
  fn   := lookaheadFn p.fn }

@[inline] def notFollowedByFn (p : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p c s;
  if s.hasError then
    s.restore iniSz iniPos
  else
    let s := s.restore iniSz iniPos;
    s.mkError "notFollowedBy"

@[inline] def notFollowedBy (p : Parser) : Parser :=
{ info := p.info,
  fn   := notFollowedByFn p.fn }

@[specialize] partial def manyAux (p : ParserFn) : ParserFn
| c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p c s;
  if s.hasError then
    if iniPos == s.pos then s.restore iniSz iniPos else s
  else if iniPos == s.pos then s.mkUnexpectedError "invalid 'many' parser combinator application, parser did not consume anything"
  else manyAux c s

@[inline] def manyFn (p : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let s := manyAux p c s;
  s.mkNode nullKind iniSz

@[inline] def many (p : Parser) : Parser :=
{ info := noFirstTokenInfo p.info,
  fn   := manyFn p.fn }

@[inline] def many1Fn (p : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let s := andthenFn p (manyAux p) c s;
  s.mkNode nullKind iniSz

@[inline] def many1 (p : Parser) : Parser :=
{ info := p.info,
  fn   := many1Fn p.fn }

@[specialize] private partial def sepByFnAux (p : ParserFn) (sep : ParserFn) (allowTrailingSep : Bool)
    (iniSz : Nat) : Bool → ParserFn
| pOpt, c, s =>
  let sz  := s.stackSize;
  let pos := s.pos;
  let s   := p c s;
  if s.hasError then
    if s.pos > pos then s
    else if pOpt then
      let s := s.restore sz pos;
      s.mkNode nullKind iniSz
    else
      -- append `Syntax.missing` to make clear that List is incomplete
      let s := s.pushSyntax Syntax.missing;
      s.mkNode nullKind iniSz
  else
    let sz  := s.stackSize;
    let pos := s.pos;
    let s   := sep c s;
    if s.hasError then
      let s := s.restore sz pos;
      s.mkNode nullKind iniSz
    else
      sepByFnAux allowTrailingSep c s

@[specialize] def sepByFn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz true c s

@[specialize] def sepBy1Fn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz false c s

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds }

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds,
  firstTokens   := p.firstTokens }

@[inline] def sepBy (p sep : Parser) (allowTrailingSep : Bool := false) : Parser :=
{ info := sepByInfo p.info sep.info,
  fn   := sepByFn allowTrailingSep p.fn sep.fn }

@[inline] def sepBy1 (p sep : Parser) (allowTrailingSep : Bool := false) : Parser :=
{ info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn }

/- Apply `f` to the syntax object produced by `p` -/
@[inline] def withResultOfFn (p : ParserFn) (f : Syntax → Syntax) : ParserFn :=
fun c s =>
  let s := p c s;
  if s.hasError then s
  else
    let stx := s.stxStack.back;
    s.popSyntax.pushSyntax (f stx)

@[noinline] def withResultOfInfo (p : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens,
  collectKinds  := p.collectKinds }

@[inline] def withResultOf (p : Parser) (f : Syntax → Syntax) : Parser :=
{ info := withResultOfInfo p.info,
  fn   := withResultOfFn p.fn f }

@[inline] def many1Unbox (p : Parser) : Parser :=
withResultOf (many1 p) fun stx => if stx.getNumArgs == 1 then stx.getArg 0 else stx

@[inline] def nodeSepBy1Unbox (k : SyntaxNodeKind) (p sep : Parser) (allowTrailingSep := false) : Parser :=
withResultOf (node k (sepBy1 p sep allowTrailingSep)) fun stx =>
  if (stx.getArg 0).getNumArgs < 2 then
    (stx.getArg 0).getArg 0
  else
    stx

@[specialize] partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn
| c, s =>
  let i := s.pos;
  if c.input.atEnd i then s.mkEOIError
  else if p (c.input.get i) then s.next c.input i
  else s.mkUnexpectedError errorMsg

@[specialize] partial def takeUntilFn (p : Char → Bool) : ParserFn
| c, s =>
  let i := s.pos;
  if c.input.atEnd i then s
  else if p (c.input.get i) then s
  else takeUntilFn c (s.next c.input i)

@[specialize] def takeWhileFn (p : Char → Bool) : ParserFn :=
takeUntilFn (fun c => !p c)

@[inline] def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : ParserFn :=
andthenFn (satisfyFn p errorMsg) (takeWhileFn p)

partial def finishCommentBlock : Nat → ParserFn
| nesting, c, s =>
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
partial def whitespace : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s
  else
    let curr := input.get i;
    if curr.isWhitespace then whitespace c (s.next input i)
    else if curr == '-' then
      let i    := input.next i;
      let curr := input.get i;
      if curr == '-' then andthenFn (takeUntilFn (fun c => c = '\n')) whitespace c (s.next input i)
      else s
    else if curr == '/' then
      let i    := input.next i;
      let curr := input.get i;
      if curr == '-' then
        let i    := input.next i;
        let curr := input.get i;
        if curr == '-' then s -- "/--" doc comment is an actual token
        else andthenFn (finishCommentBlock 1) whitespace c (s.next input i)
      else s
    else s

def mkEmptySubstringAt (s : String) (p : Nat) : Substring :=
{str := s, startPos := p, stopPos := p }

private def rawAux (startPos : Nat) (trailingWs : Bool) : ParserFn
| c, s =>
  let input   := c.input;
  let stopPos := s.pos;
  let leading := mkEmptySubstringAt input startPos;
  let val     := input.extract startPos stopPos;
  if trailingWs then
    let s        := whitespace c s;
    let stopPos' := s.pos;
    let trailing := { str := input, startPos := stopPos, stopPos := stopPos' : Substring };
    let atom     := mkAtom { leading := leading, pos := startPos, trailing := trailing } val;
    s.pushSyntax atom
  else
    let trailing := mkEmptySubstringAt input stopPos;
    let atom     := mkAtom { leading := leading, pos := startPos, trailing := trailing } val;
    s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
@[inline] def rawFn (p : ParserFn) (trailingWs := false) : ParserFn
| c, s =>
  let startPos := s.pos;
  let s := p c s;
  if s.hasError then s else rawAux startPos trailingWs c s

@[inline] def chFn (c : Char) (trailingWs := false) : ParserFn :=
rawFn (satisfyFn (fun d => c == d) ("'" ++ toString c ++ "'")) trailingWs

def rawCh (c : Char) (trailingWs := false) : Parser :=
{ fn := chFn c trailingWs }

def hexDigitFn : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let i    := input.next i;
    if curr.isDigit || ('a' <= curr && curr <= 'f') || ('A' <= curr && curr <= 'F') then s.setPos i
    else s.mkUnexpectedError "invalid hexadecimal numeral"

def quotedCharFn : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    if curr == '\\' || curr == '\"' || curr == '\'' || curr == 'r' || curr == 'n' || curr == 't' then
      s.next input i
    else if curr == 'x' then
      andthenFn hexDigitFn hexDigitFn c (s.next input i)
    else if curr == 'u' then
      andthenFn hexDigitFn (andthenFn hexDigitFn (andthenFn hexDigitFn hexDigitFn)) c (s.next input i)
    else
      s.mkUnexpectedError "invalid escape sequence"

/-- Push `(Syntax.node tk <new-atom>)` into syntax stack -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : Nat) : ParserFn :=
fun c s =>
let input     := c.input;
let stopPos   := s.pos;
let leading   := mkEmptySubstringAt input startPos;
let val       := input.extract startPos stopPos;
let s         := whitespace c s;
let wsStopPos := s.pos;
let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring };
let info      := { leading := leading, pos := startPos, trailing := trailing : SourceInfo };
s.pushSyntax (mkStxLit n val info)

def charLitFnAux (startPos : Nat) : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let s    := s.setPos (input.next i);
    let s    := if curr == '\\' then quotedCharFn c s else s;
    if s.hasError then s
    else
      let i    := s.pos;
      let curr := input.get i;
      let s    := s.setPos (input.next i);
      if curr == '\'' then mkNodeToken charLitKind startPos c s
      else s.mkUnexpectedError "missing end of character literal"

partial def strLitFnAux (startPos : Nat) : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let s    := s.setPos (input.next i);
    if curr == '\"' then
      mkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenFn quotedCharFn strLitFnAux c s
    else strLitFnAux c s

def decimalNumberFn (startPos : Nat) : ParserFn :=
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

def binNumberFn (startPos : Nat) : ParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "binary number" c s;
  mkNodeToken numLitKind startPos c s

def octalNumberFn (startPos : Nat) : ParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "octal number" c s;
  mkNodeToken numLitKind startPos c s

def hexNumberFn (startPos : Nat) : ParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" c s;
  mkNodeToken numLitKind startPos c s

def numberFnAux : ParserFn :=
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
      s.mkError "numeral"

def isIdCont : String → ParserState → Bool
| input, s =>
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

private def isToken (idStartPos idStopPos : Nat) (tk : Option Token) : Bool :=
match tk with
| none    => false
| some tk =>
   -- if a token is both a symbol and a valid identifier (i.e. a keyword),
   -- we want it to be recognized as a symbol
  tk.bsize ≥ idStopPos - idStartPos

def mkTokenAndFixPos (startPos : Nat) (tk : Option Token) : ParserFn :=
fun c s =>
match tk with
| none    => s.mkErrorAt "token" startPos
| some tk =>
  let input     := c.input;
  let leading   := mkEmptySubstringAt input startPos;
  let stopPos   := startPos + tk.bsize;
  let s         := s.setPos stopPos;
  let s         := whitespace c s;
  let wsStopPos := s.pos;
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring };
  let atom      := mkAtom { leading := leading, pos := startPos, trailing := trailing } tk;
  s.pushSyntax atom

def mkIdResult (startPos : Nat) (tk : Option Token) (val : Name) : ParserFn :=
fun c s =>
let stopPos           := s.pos;
if isToken startPos stopPos tk then
  mkTokenAndFixPos startPos tk c s
else
  let input           := c.input;
  let rawVal          := { str := input, startPos := startPos, stopPos := stopPos  : Substring };
  let s               := whitespace c s;
  let trailingStopPos := s.pos;
  let leading         := mkEmptySubstringAt input startPos;
  let trailing        := { str := input, startPos := stopPos, stopPos := trailingStopPos : Substring };
  let info            := { leading := leading, trailing := trailing, pos := startPos : SourceInfo };
  let atom            := mkIdent info rawVal val;
  s.pushSyntax atom

partial def identFnAux (startPos : Nat) (tk : Option Token) : Name → ParserFn
| r, c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    if isIdBeginEscape curr then
      let startPart := input.next i;
      let s         := takeUntilFn isIdEndEscape c (s.setPos startPart);
      let stopPart  := s.pos;
      let s         := satisfyFn isIdEndEscape "missing end of escaped identifier" c s;
      if s.hasError then s
      else
        let r := mkNameStr r (input.extract startPart stopPart);
        if isIdCont input s then
          let s := s.next input s.pos;
          identFnAux r c s
        else
          mkIdResult startPos tk r c s
    else if isIdFirst curr then
      let startPart := i;
      let s         := takeWhileFn isIdRest c (s.next input i);
      let stopPart  := s.pos;
      let r := mkNameStr r (input.extract startPart stopPart);
      if isIdCont input s then
        let s := s.next input s.pos;
        identFnAux r c s
      else
        mkIdResult startPos tk r c s
    else
      mkTokenAndFixPos startPos tk c s

private def isIdFirstOrBeginEscape (c : Char) : Bool :=
isIdFirst c || isIdBeginEscape c

private def nameLitAux (startPos : Nat) : ParserFn
| c, s =>
  let input := c.input;
  let s     := identFnAux startPos none Name.anonymous c (s.next input startPos);
  if s.hasError then
    s.mkErrorAt "invalid Name literal" startPos
  else
    let stx := s.stxStack.back;
    match stx with
    | Syntax.ident _ rawStr _ _ =>
      let s := s.popSyntax;
      s.pushSyntax (Syntax.node nameLitKind #[mkAtomFrom stx rawStr.toString])
    | _ => s.mkError "invalid Name literal"

private def tokenFnAux : ParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  let curr  := input.get i;
  if curr == '\"' then
    strLitFnAux i c (s.next input i)
  else if curr == '\'' then
    charLitFnAux i c (s.next input i)
  else if curr.isDigit then
    numberFnAux c s
  else if curr == '`' && isIdFirstOrBeginEscape (getNext input i) then
    nameLitAux i c s
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

def tokenFn : ParserFn :=
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

def peekTokenAux (c : ParserContext) (s : ParserState) : ParserState × Option Syntax :=
let iniSz  := s.stackSize;
let iniPos := s.pos;
let s      := tokenFn c s;
if s.hasError then (s.restore iniSz iniPos, none)
else
  let stx := s.stxStack.back;
  (s.restore iniSz iniPos, some stx)

@[inline] def peekToken (c : ParserContext) (s : ParserState) : ParserState × Option Syntax :=
let tkc := s.cache.tokenCache;
if tkc.startPos == s.pos then
  (s, some tkc.token)
else
  peekTokenAux c s

/- Treat keywords as identifiers. -/
def rawIdentFn : ParserFn :=
fun c s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else identFnAux i none Name.anonymous c s

@[inline] def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn :=
fun c s =>
  let startPos := s.pos;
  let s        := tokenFn c s;
  if s.hasError then
    s.mkErrorsAt expected startPos
  else
    match s.stxStack.back with
    | Syntax.atom _ sym => if p sym then s else s.mkErrorsAt expected startPos
    | _                 => s.mkErrorsAt expected startPos

@[inline] def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolInfo (sym : String) : ParserInfo :=
{ collectTokens := fun tks => sym :: tks,
  firstTokens   := FirstTokens.tokens [ sym ] }

@[inline] def symbolFn (sym : String) : ParserFn :=
symbolFnAux sym ("'" ++ sym ++ "'")

@[inline] def symbol (sym : String) : Parser :=
let sym := sym.trim;
{ info := symbolInfo sym,
  fn   := symbolFn sym }

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` Function is parsed using this combinator so that
    it can still be used as an identifier outside of universes (but registering it
    as a token in a Term Syntax would not break the universe Parser). -/
def nonReservedSymbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
fun c s =>
  let startPos := s.pos;
  let s := tokenFn c s;
  if s.hasError then s.mkErrorAt errorMsg startPos
  else
    match s.stxStack.back with
    | Syntax.atom _ sym' =>
      if sym == sym' then s else s.mkErrorAt errorMsg startPos
    | Syntax.ident info rawVal _ _ =>
      if sym == rawVal.toString then
        let s := s.popSyntax;
        s.pushSyntax (Syntax.atom info sym)
      else
        s.mkErrorAt errorMsg startPos
    | _ => s.mkErrorAt errorMsg startPos

@[inline] def nonReservedSymbolFn (sym : String) : ParserFn :=
nonReservedSymbolFnAux sym ("'" ++ sym ++ "'")

def nonReservedSymbolInfo (sym : String) (includeIdent : Bool) : ParserInfo :=
{ firstTokens  :=
  if includeIdent then
    FirstTokens.tokens [ sym, "ident" ]
  else
    FirstTokens.tokens [ sym ] }

@[inline] def nonReservedSymbol (sym : String) (includeIdent := false) : Parser :=
let sym := sym.trim;
{ info := nonReservedSymbolInfo sym includeIdent,
  fn   := nonReservedSymbolFn sym }

partial def strAux (sym : String) (errorMsg : String) : Nat → ParserFn
| j, c, s =>
  if sym.atEnd j then s
  else
    let i := s.pos;
    let input := c.input;
    if input.atEnd i || sym.get j != input.get i then s.mkError errorMsg
    else strAux (sym.next j) c (s.next input i)

def checkTailWs (prev : Syntax) : Bool :=
match prev.getTailInfo with
| some { trailing := some trailing, .. } => trailing.stopPos > trailing.startPos
| _                                      => false

def checkWsBeforeFn (errorMsg : String) : ParserFn :=
fun c s =>
  let prev := s.stxStack.back;
  if checkTailWs prev then s else s.mkError errorMsg

def checkWsBefore (errorMsg : String) : Parser :=
{ info := epsilonInfo,
  fn   := checkWsBeforeFn errorMsg }

def checkTailNoWs (prev : Syntax) : Bool :=
match prev.getTailInfo with
| some { trailing := some trailing, .. } => trailing.stopPos == trailing.startPos
| _                                      => false

private def pickNonNone (stack : Array Syntax) : Syntax :=
match stack.findRev? $ fun stx => !stx.isNone with
| none => Syntax.missing
| some stx => stx

def checkNoWsBeforeFn (errorMsg : String) : ParserFn :=
fun c s =>
  let prev := pickNonNone s.stxStack;
  if checkTailNoWs prev then s else s.mkError errorMsg

def checkNoWsBefore (errorMsg : String) : Parser :=
{ info := epsilonInfo,
  fn   := checkNoWsBeforeFn errorMsg }

def symbolNoWsInfo (sym : String) : ParserInfo :=
{ collectTokens := fun tks => sym :: tks,
  firstTokens   := FirstTokens.tokens [ sym ] }

@[inline] def symbolNoWsFnAux (sym : String) (errorMsg : String) : ParserFn :=
fun c s =>
  let left := s.stxStack.back;
  if checkTailNoWs left then
    let startPos := s.pos;
    let input    := c.input;
    let s        := strAux sym errorMsg 0 c s;
    if s.hasError then s
    else
      let leading   := mkEmptySubstringAt input startPos;
      let stopPos   := startPos + sym.bsize;
      let trailing  := mkEmptySubstringAt input stopPos;
      let atom      := mkAtom { leading := leading, pos := startPos, trailing := trailing } sym;
      s.pushSyntax atom
  else
    s.mkError errorMsg

@[inline] def symbolNoWsFn (sym : String) : ParserFn :=
symbolNoWsFnAux sym ("'" ++ sym ++ "' without whitespace around it")

/- Similar to `symbol`, but succeeds only if there is no space whitespace after leading term and after `sym`. -/
@[inline] def symbolNoWs (sym : String) : Parser :=
let sym := sym.trim;
{ info := symbolNoWsInfo sym,
  fn   := symbolNoWsFn sym }

def unicodeSymbolFnAux (sym asciiSym : String) (expected : List String) : ParserFn :=
satisfySymbolFn (fun s => s == sym || s == asciiSym) expected

def unicodeSymbolInfo (sym asciiSym : String) : ParserInfo :=
{ collectTokens := fun tks => sym :: asciiSym :: tks,
  firstTokens   := FirstTokens.tokens [ sym, asciiSym ] }

@[inline] def unicodeSymbolFn (sym asciiSym : String) : ParserFn :=
unicodeSymbolFnAux sym asciiSym ["'" ++ sym ++ "', '" ++ asciiSym ++ "'"]

@[inline] def unicodeSymbol (sym asciiSym : String) : Parser :=
let sym := sym.trim;
let asciiSym := asciiSym.trim;
{ info := unicodeSymbolInfo sym asciiSym,
  fn   := unicodeSymbolFn sym asciiSym }

def mkAtomicInfo (k : String) : ParserInfo :=
{ firstTokens := FirstTokens.tokens [ k ] }

def numLitFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind numLitKind) then s.mkErrorAt "numeral" iniPos else s

@[inline] def numLitNoAntiquot : Parser :=
{ fn   := numLitFn,
  info := mkAtomicInfo "numLit" }

def strLitFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "string literal" iniPos else s

@[inline] def strLitNoAntiquot : Parser :=
{ fn   := strLitFn,
  info := mkAtomicInfo "strLit" }

def charLitFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind charLitKind) then s.mkErrorAt "character literal" iniPos else s

@[inline] def charLitNoAntiquot : Parser :=
{ fn   := charLitFn,
  info := mkAtomicInfo "charLit" }

def nameLitFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind nameLitKind) then s.mkErrorAt "Name literal" iniPos else s

@[inline] def nameLitNoAntiquot : Parser :=
{ fn   := nameLitFn,
  info := mkAtomicInfo "nameLit" }

def identFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isIdent) then s.mkErrorAt "identifier" iniPos else s

@[inline] def identNoAntiquot : Parser :=
{ fn   := identFn,
  info := mkAtomicInfo "ident" }

@[inline] def rawIdentNoAntiquot : Parser :=
{ fn := rawIdentFn }

def identEqFn (id : Name) : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError then
    s.mkErrorAt "identifier" iniPos
  else match s.stxStack.back with
    | Syntax.ident _ _ val _ => if val != id then s.mkErrorAt ("expected identifier '" ++ toString id ++ "'") iniPos else s
    | _ => s.mkErrorAt "identifier" iniPos

@[inline] def identEq (id : Name) : Parser :=
{ fn   := identEqFn id,
  info := mkAtomicInfo "ident" }

def quotedSymbolFn : ParserFn :=
nodeFn quotedSymbolKind (andthenFn (andthenFn (chFn '`') (rawFn (takeUntilFn (fun c => c == '`')))) (chFn '`' true))

-- TODO: remove after old frontend is gone
def quotedSymbol : Parser :=
{ fn := quotedSymbolFn }

def unquotedSymbolFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || s.stxStack.back.isIdent || isLitKind s.stxStack.back.getKind then
    s.mkErrorAt "symbol" iniPos
  else
    s

def unquotedSymbol : Parser :=
{ fn := unquotedSymbolFn }

instance stringToParserCoeOld : HasCoe String Parser := ⟨fun s => symbol s ⟩
instance stringToParserCoe : Coe String Parser := ⟨fun s => symbol s ⟩

namespace ParserState

def keepNewError (s : ParserState) (oldStackSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, err⟩ => ⟨stack.shrink oldStackSize, pos, cache, err⟩

def keepPrevError (s : ParserState) (oldStackSize : Nat) (oldStopPos : String.Pos) (oldError : Option Error) : ParserState :=
match s with
| ⟨stack, _, cache, _⟩ => ⟨stack.shrink oldStackSize, oldStopPos, cache, oldError⟩

def mergeErrors (s : ParserState) (oldStackSize : Nat) (oldError : Error) : ParserState :=
match s with
| ⟨stack, pos, cache, some err⟩ =>
  if oldError == err then s
  else ⟨stack.shrink oldStackSize, pos, cache, some (oldError.merge err)⟩
| other                         => other

def keepLatest (s : ParserState) (startStackSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ =>
  let node  := stack.back;
  let stack := stack.shrink startStackSize;
  let stack := stack.push node;
  ⟨stack, pos, cache, none⟩

def replaceLongest (s : ParserState) (startStackSize : Nat) : ParserState :=
s.keepLatest startStackSize

end ParserState

def invalidLongestMatchParser (s : ParserState) : ParserState :=
s.mkError "longestMatch parsers must generate exactly one Syntax node"

/--
 Auxiliary function used to execute parsers provided to `longestMatchFn`.
 Push `left?` into the stack if it is not `none`, and execute `p`.
 After executing `p`, remove `left`.

 Remark: `p` must produce exactly one syntax node.
 Remark: the `left?` is not none when we are processing trailing parsers. -/
@[inline] def runLongestMatchParser (left? : Option Syntax) (p : ParserFn) : ParserFn :=
fun c s =>
  let startSize := s.stackSize;
  match left? with
  | none      =>
    let s := p c s;
    if s.hasError then s
    else
      -- stack contains `[..., result ]`
      if s.stackSize == startSize + 1 then
        s
      else
        invalidLongestMatchParser s
  | some left =>
    let s         := s.pushSyntax left;
    let s         := p c s;
    if s.hasError then s
    else
      -- stack contains `[..., left, result ]` we must remove `left`
      if s.stackSize == startSize + 2 then
        -- `p` created one node, then we just remove `left` and keep it
        let r := s.stxStack.back;
        let s := s.shrinkStack startSize; -- remove `r` and `left`
        s.pushSyntax r -- add `r` back
      else
        invalidLongestMatchParser s

def longestMatchStep (left? : Option Syntax) (startSize : Nat) (startPos : String.Pos) (p : ParserFn) : ParserFn :=
fun c s =>
let prevErrorMsg  := s.errorMsg;
let prevStopPos   := s.pos;
let prevSize      := s.stackSize;
let s             := s.restore prevSize startPos;
let s             := runLongestMatchParser left? p c s;
match prevErrorMsg, s.errorMsg with
| none, none   => -- both succeeded
  if s.pos > prevStopPos      then s.replaceLongest startSize
  else if s.pos < prevStopPos then s.restore prevSize prevStopPos -- keep prev
  else s
| none, some _ => -- prev succeeded, current failed
  s.restore prevSize prevStopPos
| some oldError, some _ => -- both failed
  if s.pos > prevStopPos      then s.keepNewError prevSize
  else if s.pos < prevStopPos then s.keepPrevError prevSize prevStopPos prevErrorMsg
  else s.mergeErrors prevSize oldError
| some _, none => -- prev failed, current succeeded
  let successNode := s.stxStack.back;
  let s           := s.shrinkStack startSize; -- restore stack to initial size to make sure (failure) nodes are removed from the stack
  s.pushSyntax successNode -- put successNode back on the stack

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
if !s.hasError && s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux (left? : Option Syntax) (startSize : Nat) (startPos : String.Pos) : List Parser → ParserFn
| []    => fun _ s => longestMatchMkResult startSize s
| p::ps => fun c s =>
   let s := longestMatchStep left? startSize startPos p.fn c s;
   longestMatchFnAux ps c s

def longestMatchFn (left? : Option Syntax) : List Parser → ParserFn
| []    => fun _ s => s.mkError "longestMatch: empty list"
| [p]   => runLongestMatchParser left? p.fn
| p::ps => fun c s =>
  let startSize := s.stackSize;
  let startPos  := s.pos;
  let s         := runLongestMatchParser left? p.fn c s;
  if s.hasError then
    let s := s.shrinkStack startSize;
    longestMatchFnAux left? startSize startPos ps c s
  else
    longestMatchFnAux left? startSize startPos ps c s

def anyOfFn : List Parser → ParserFn
| [],    _, s => s.mkError "anyOf: empty list"
| [p],   c, s => p.fn c s
| p::ps, c, s => orelseFn p.fn (anyOfFn ps) c s

@[inline] def checkColGeFn (col : Nat) (errorMsg : String) : ParserFn :=
fun c s =>
  let pos := c.fileMap.toPosition s.pos;
  if pos.column ≥ col then s
  else s.mkError errorMsg

@[inline] def checkColGe (col : Nat) (errorMsg : String) : Parser :=
{ fn := checkColGeFn col errorMsg }

@[inline] def withPosition (p : Position → Parser) : Parser :=
{ info := (p { line := 1, column := 0 }).info,
  fn   := fun c s =>
   let pos := c.fileMap.toPosition s.pos;
   (p pos).fn c s }

@[inline] def many1Indent (p : Parser) (errorMsg : String) : Parser :=
withPosition $ fun pos => many1 (checkColGe pos.column errorMsg >> p)

open Std (RBMap RBMap.empty)

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickLt

namespace TokenMap

def insert {α : Type} (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
match map.find? k with
| none    => map.insert k [v]
| some vs => map.insert k (v::vs)

instance {α : Type} : Inhabited (TokenMap α) := ⟨RBMap.empty⟩

instance {α : Type} : HasEmptyc (TokenMap α) := ⟨RBMap.empty⟩

end TokenMap

structure PrattParsingTables :=
(leadingTable    : TokenMap Parser := {})
(leadingParsers  : List Parser := []) -- for supporting parsers we cannot obtain first token
(trailingTable   : TokenMap TrailingParser := {})
(trailingParsers : List TrailingParser := []) -- for supporting parsers such as function application

instance PrattParsingTables.inhabited : Inhabited PrattParsingTables := ⟨{}⟩

/--
  Each parser category is implemented using a Pratt's parser.
  The system comes equipped with the following categories: `level`, `term`, `tactic`, and `command`.
  Users and plugins may define extra categories.

  The field `leadingIdentAsSymbol` specifies how the parsing table
  lookup function behaves for identifiers.  The function `prattParser`
  uses two tables `leadingTable` and `trailingTable`. They map tokens
  to parsers. If `leadingIdentAsSymbol == false` and the leading token
  is an identifier, then `prattParser` just executes the parsers
  associated with the auxiliary token "ident".  If
  `leadingIdentAsSymbol == true` and the leading token is an
  identifier `<foo>`, then `prattParser` combines the parsers
  associated with the token `<foo>` with the parsers associated with
  the auxiliary token "ident".  We use this feature and the
  `nonReservedSymbol` parser to implement the `tactic` parsers.  We
  use this approach to avoid creating a reserved symbol for each
  builtin tactic (e.g., `apply`, `assumption`, etc.).  That is, users
  may still use these symbols as identifiers (e.g., naming a
  function).

  The method
  ```
  categoryParser `term prec
  ```
  executes the Pratt's parser for category `term` with precedence `prec`.
  That is, only parsers with precedence at least `prec` are considered.
  The method `termParser prec` is equivalent to the method above.
-/
structure ParserCategory :=
(tables : PrattParsingTables) (leadingIdentAsSymbol : Bool)

instance ParserCategory.inhabited : Inhabited ParserCategory := ⟨{ tables := {}, leadingIdentAsSymbol := false }⟩

abbrev ParserCategories := Std.PersistentHashMap Name ParserCategory

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (leadingIdentAsSymbol : Bool) : ParserState × List α :=
let (s, stx) := peekToken c s;
let find (n : Name) : ParserState × List α :=
  match map.find? n with
  | some as => (s, as)
  | _       => (s, []);
match stx with
| some (Syntax.atom _ sym)      => find (mkNameSimple sym)
| some (Syntax.ident _ _ val _) =>
  if leadingIdentAsSymbol then
    match map.find? val with
    | some as => match map.find? identKind with
      | some as' => (s, as ++ as')
      | _        => (s, as)
    | none    => find identKind
  else
    find identKind
| some (Syntax.node k _)        => find k
| _                             => (s, [])

abbrev CategoryParserFn := Name → ParserFn

def mkCategoryParserFnRef : IO (IO.Ref CategoryParserFn) :=
IO.mkRef $ fun _ => whitespace

@[init mkCategoryParserFnRef]
constant categoryParserFnRef : IO.Ref CategoryParserFn := arbitrary _

def mkCategoryParserFnExtension : IO (EnvExtension CategoryParserFn) :=
registerEnvExtension $ categoryParserFnRef.get

@[init mkCategoryParserFnExtension]
def categoryParserFnExtension : EnvExtension CategoryParserFn := arbitrary _

def categoryParserFn (catName : Name) : ParserFn :=
fun ctx s => categoryParserFnExtension.getState ctx.env catName ctx s

def categoryParser (catName : Name) (prec : Nat) : Parser :=
{ fn := fun c s => categoryParserFn catName { c with prec := prec } s }

-- Define `termParser` here because we need it for antiquotations
@[inline] def termParser (prec : Nat := 0) : Parser :=
categoryParser `term prec

/- ============== -/
/- Antiquotations -/
/- ============== -/

def dollarSymbol : Parser := symbol "$"

/-- Fail if previous token is immediately followed by ':'. -/
def checkNoImmediateColon : Parser :=
{ fn := fun c s =>
  let prev := s.stxStack.back;
  if checkTailNoWs prev then
    let input := c.input;
    let i     := s.pos;
    if input.atEnd i then s
    else
      let curr := input.get i;
      if curr == ':' then
        s.mkUnexpectedError "unexpected ':'"
      else s
  else s
}

def setExpectedFn (expected : List String) (p : ParserFn) : ParserFn :=
fun c s => match p c s with
  | s'@{ errorMsg := some msg, .. } => { s' with errorMsg := some { msg with expected := [] } }
  | s'                              => s'

def setExpected (expected : List String) (p : Parser) : Parser :=
{ fn := setExpectedFn expected p.fn, info := p.info }

def pushNone : Parser :=
{ fn := fun c s => s.pushSyntax mkNullNode }

-- We support two kinds of antiquotations: `$id` and `$(t)`, where `id` is a term identifier and `t` is a term.
def antiquotNestedExpr : Parser := node `antiquotNestedExpr (symbol "(" >> toggleInsideQuot termParser >> ")")
def antiquotExpr : Parser       := identNoAntiquot <|> antiquotNestedExpr

/--
  Define parser for `$e` (if anonymous == true) and `$e:name`. Both
  forms can also be used with an appended `*` to turn them into an
  antiquotation "splice". If `kind` is given, it will additionally be checked
  when evaluating `match_syntax`. Antiquotations can be escaped as in `$$e`, which
  produces the syntax tree for `$e`. -/
def mkAntiquot (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parser :=
let kind := (kind.getD Name.anonymous) ++ `antiquot;
let nameP := node `antiquotName $ checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbol ":" >> nonReservedSymbol name;
-- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
-- antiquotation kind via `noImmediateColon`
let nameP := if anonymous then nameP <|> checkNoImmediateColon >> pushNone else nameP;
-- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
node kind $ try $
  setExpected [] dollarSymbol >>
  many (checkNoWsBefore "" >> dollarSymbol) >>
  checkNoWsBefore "no space before spliced term" >> antiquotExpr >>
  nameP >>
  optional (checkNoWsBefore "" >> symbol "*")

def tryAnti (c : ParserContext) (s : ParserState) : Bool :=
let (s, stx?) := peekToken c s;
match stx? with
| some stx@(Syntax.atom _ sym) => sym == "$"
| _                            => false

@[inline] def withAntiquotFn (antiquotP p : ParserFn) : ParserFn :=
fun c s => if tryAnti c s then orelseFn antiquotP p c s else p c s

/-- Optimized version of `mkAntiquot ... <|> p`. -/
@[inline] def withAntiquot (antiquotP p : Parser) : Parser :=
{ fn := withAntiquotFn antiquotP.fn p.fn,
  info := orelseInfo antiquotP.info p.info }

/- ===================== -/
/- End of Antiquotations -/
/- ===================== -/

def nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : Parser) : Parser :=
withAntiquot (mkAntiquot name kind false) $ node kind p

def ident : Parser :=
withAntiquot (mkAntiquot "ident" identKind) identNoAntiquot

-- `ident` and `rawIdent` produce the same syntax tree, so we reuse the antiquotation kind name
def rawIdent : Parser :=
withAntiquot (mkAntiquot "ident" identKind) rawIdentNoAntiquot

def numLit : Parser :=
withAntiquot (mkAntiquot "numLit" numLitKind) numLitNoAntiquot

def strLit : Parser :=
withAntiquot (mkAntiquot "strLit" strLitKind) strLitNoAntiquot

def charLit : Parser :=
withAntiquot (mkAntiquot "charLit" charLitKind) charLitNoAntiquot

def nameLit : Parser :=
withAntiquot (mkAntiquot "nameLit" nameLitKind) nameLitNoAntiquot

def categoryParserOfStackFn (offset : Nat) : ParserFn :=
fun ctx s =>
  let stack := s.stxStack;
  if stack.size < offset + 1 then
    s.mkUnexpectedError ("failed to determine parser category using syntax stack, stack is too small")
  else
    match stack.get! (stack.size - offset - 1) with
    | Syntax.ident _ _ catName _ => categoryParserFn catName ctx s
    | _ => s.mkUnexpectedError ("failed to determine parser category using syntax stack, the specified element on the stack is not an identifier")

def categoryParserOfStack (offset : Nat) (prec : Nat := 0) : Parser :=
{ fn := fun c s => categoryParserOfStackFn offset { c with prec := prec } s }

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
if s.stackSize == iniSz + 1 then s
else s.mkNode nullKind iniSz -- throw error instead?

def leadingParserAux (kind : Name) (tables : PrattParsingTables) (leadingIdentAsSymbol : Bool) : ParserFn :=
fun c s =>
  let iniSz   := s.stackSize;
  let (s, ps) := indexed tables.leadingTable c s leadingIdentAsSymbol;
  let ps      := tables.leadingParsers ++ ps;
  if ps.isEmpty then
    s.mkError (toString kind)
  else
    let s := longestMatchFn none ps c s;
    mkResult s iniSz

@[inline] def leadingParser (kind : Name) (tables : PrattParsingTables) (leadingIdentAsSymbol : Bool) (antiquotParser : ParserFn) : ParserFn :=
withAntiquotFn antiquotParser (leadingParserAux kind tables leadingIdentAsSymbol)

def trailingLoopStep (tables : PrattParsingTables) (left : Syntax) (ps : List Parser) : ParserFn :=
fun c s => longestMatchFn left (ps ++ tables.trailingParsers) c s

private def mkTrailingResult (s : ParserState) (iniSz : Nat) : ParserState :=
let s := mkResult s iniSz;
-- Stack contains `[..., left, result]`
-- We must remove `left`
let result := s.stxStack.back;
let s      := s.popSyntax.popSyntax;
s.pushSyntax result

partial def trailingLoop (tables : PrattParsingTables) (c : ParserContext) : ParserState → ParserState
| s =>
  let identAsSymbol := false;
  let (s, ps)       := indexed tables.trailingTable c s identAsSymbol;
  if ps.isEmpty && tables.trailingParsers.isEmpty then
    s -- no available trailing parser
  else
    let left   := s.stxStack.back;
    let iniSz  := s.stackSize;
    let iniPos := s.pos;
    let s      := trailingLoopStep tables left ps c s;
    if s.hasError then
      if s.pos == iniPos then s.restore iniSz iniPos else s
    else
      let s := mkTrailingResult s iniSz;
      trailingLoop s

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
@[inline] def prattParser (kind : Name) (tables : PrattParsingTables) (leadingIdentAsSymbol : Bool) (antiquotParser : ParserFn) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s := leadingParser kind tables leadingIdentAsSymbol antiquotParser c s;
  if s.hasError then
    s
  else
    trailingLoop tables c s


def fieldIdxFn : ParserFn :=
fun c s =>
  let iniPos := s.pos;
  let curr     := c.input.get iniPos;
  if curr.isDigit && curr != '0' then
    let s     := takeWhileFn (fun c => c.isDigit) c s;
    mkNodeToken fieldIdxKind iniPos c s
  else
    s.mkErrorAt "field index" iniPos

@[inline] def fieldIdx : Parser :=
withAntiquot (mkAntiquot "fieldIdx" `fieldIdx)
  { fn   := fieldIdxFn,
    info := mkAtomicInfo "fieldIdx" }

@[inline] def skip : Parser :=
{ fn   := fun c s => s,
  info := epsilonInfo }

/-- No-op parser that advises the pretty printer to emit a non-breaking space. -/
@[inline] def ppHardSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a space/soft line break. -/
@[inline] def ppSpace : Parser := skip
/-- No-op parser that advises the pretty printer to emit a hard line break. -/
@[inline] def ppLine : Parser := skip
/--
  No-op parser combinator that advises the pretty printer to group and indent the given syntax.
  By default, only syntax categories are grouped. -/
@[inline] def ppGroup : Parser → Parser := id

end Parser

namespace Syntax

section
variables {β : Type} {m : Type → Type} [Monad m]

@[inline] def foldArgsM (s : Syntax) (f : Syntax → β → m β) (b : β) : m β :=
s.getArgs.foldlM (flip f) b

@[inline] def foldArgs (s : Syntax) (f : Syntax → β → β) (b : β) : β :=
Id.run (s.foldArgsM f b)

@[inline] def forArgsM (s : Syntax) (f : Syntax → m Unit) : m Unit :=
s.foldArgsM (fun s _ => f s) ()

@[inline] def foldSepArgsM (s : Syntax) (f : Syntax → β → m β) (b : β) : m β :=
s.getArgs.foldlStepM (flip f) b 2

@[inline] def foldSepArgs (s : Syntax) (f : Syntax → β → β) (b : β) : β :=
Id.run (s.foldSepArgsM f b)

@[inline] def forSepArgsM (s : Syntax) (f : Syntax → m Unit) : m Unit :=
s.foldSepArgsM (fun s _ => f s) ()

@[inline] def foldSepRevArgsM (s : Syntax) (f : Syntax → β → m β) (b : β) : m β := do
let args := foldSepArgs s (fun arg (args : Array Syntax) => args.push arg) #[];
args.foldrM f b

@[inline] def foldSepRevArgs (s : Syntax) (f : Syntax → β → β) (b : β) : β := do
Id.run $ foldSepRevArgsM s f b

end

end Syntax
end Lean

section
variables {β : Type} {m : Type → Type} [Monad m]
open Lean
open Lean.Syntax

@[inline] def Array.foldSepByM (args : Array Syntax) (f : Syntax → β → m β) (b : β) : m β :=
args.foldlStepM (flip f) b 2

@[inline] def Array.foldSepBy (args : Array Syntax) (f : Syntax → β → β) (b : β) : β :=
Id.run $ args.foldSepByM f b
end
