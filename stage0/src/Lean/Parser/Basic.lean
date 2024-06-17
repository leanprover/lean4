/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Data.Trie
import Lean.Data.Position
import Lean.Syntax
import Lean.ToExpr
import Lean.Environment
import Lean.Attributes
import Lean.Message
import Lean.Compiler.InitAttr
import Lean.ResolveName

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
This is the only case where standard parsers might execute arbitrary backtracking. At the moment there is no memoization shared by these
parallel parsers apart from the first token, though we might change this in the future if the need arises.

Finally, error reporting follows the standard combinatoric approach of collecting a single unexpected token/... and zero
or more expected tokens (see `Error` below). Expected tokens are e.g. set by `symbol` and merged by `<|>`. Combinators
running multiple parsers should check if an error message is set in the parser state (`hasError`) and act accordingly.
Error recovery is left to the designer of the specific language; for example, Lean's top-level `parseCommand` loop skips
tokens until the next command keyword on error.
-/

namespace Lean

namespace Parser

def isLitKind (k : SyntaxNodeKind) : Bool :=
  k == strLitKind || k == numLitKind || k == charLitKind || k == nameLitKind || k == scientificLitKind

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
def maxPrec  : Nat := eval_prec max
def argPrec  : Nat := eval_prec arg
def leadPrec : Nat := eval_prec lead
def minPrec  : Nat := eval_prec min

abbrev Token := String

structure TokenCacheEntry where
  startPos : String.Pos := 0
  stopPos  : String.Pos := 0
  token    : Syntax := Syntax.missing

structure ParserCache where
  tokenCache : TokenCacheEntry

def initCacheForInput (input : String) : ParserCache := {
  tokenCache := { startPos := input.bsize + 1 /- make sure it is not a valid position -/}
}

abbrev TokenTable := Trie Token

abbrev SyntaxNodeKindSet := Std.PersistentHashMap SyntaxNodeKind Unit

def SyntaxNodeKindSet.insert (s : SyntaxNodeKindSet) (k : SyntaxNodeKind) : SyntaxNodeKindSet :=
  Std.PersistentHashMap.insert s k ()

/-
  Input string and related data. Recall that the `FileMap` is a helper structure for mapping
  `String.Pos` in the input string to line/column information.  -/
structure InputContext where
  input    : String
  fileName : String
  fileMap  : FileMap
  deriving Inhabited

/-- Input context derived from elaboration of previous commands. -/
structure ParserModuleContext where
  env           : Environment
  options       : Options
  -- for name lookup
  currNamespace : Name := Name.anonymous
  openDecls     : List OpenDecl := []

structure ParserContext extends InputContext, ParserModuleContext where
  prec               : Nat
  tokens             : TokenTable
  quotDepth          : Nat := 0
  suppressInsideQuot : Bool := false
  savedPos?          : Option String.Pos := none
  forbiddenTk?       : Option Token := none

def ParserContext.resolveName (ctx : ParserContext) (id : Name) : List (Name × List String) :=
  ResolveName.resolveGlobalName ctx.env ctx.currNamespace ctx.openDecls id

structure Error where
  unexpected : String := ""
  expected : List String := []
  deriving Inhabited, BEq

namespace Error

private def expectedToString : List String → String
  | []       => ""
  | [e]      => e
  | [e1, e2] => e1 ++ " or " ++ e2
  | e::es    => e ++ ", " ++ expectedToString es

protected def toString (e : Error) : String :=
  let unexpected := if e.unexpected == "" then [] else [e.unexpected]
  let expected   := if e.expected == [] then [] else
    let expected := e.expected.toArray.qsort (fun e e' => e < e')
    let expected := expected.toList.eraseReps
    ["expected " ++ expectedToString expected]
  "; ".intercalate $ unexpected ++ expected

instance : ToString Error := ⟨Error.toString⟩

def merge (e₁ e₂ : Error) : Error :=
  match e₂ with
  | { unexpected := u, .. } => { unexpected := if u == "" then e₁.unexpected else u, expected := e₁.expected ++ e₂.expected }

end Error

structure ParserState where
  stxStack : Array Syntax := #[]
  /--
    Set to the precedence of the preceding (not surrounding) parser by `runLongestMatchParser`
    for the use of `checkLhsPrec` in trailing parsers.
    Note that with chaining, the preceding parser can be another trailing parser:
    in `1 * 2 + 3`, the preceding parser is '*' when '+' is executed. -/
  lhsPrec  : Nat := 0
  pos      : String.Pos := 0
  cache    : ParserCache
  errorMsg : Option Error := none

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
    let pos := ctx.fileMap.toPosition s.pos
    mkErrorStringWithPos ctx.fileName pos (toString msg)

def mkNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    if err != none && stack.size == iniStackSz then
      -- If there is an error but there are no new nodes on the stack, use `missing` instead.
      -- Thus we ensure the property that an syntax tree contains (at least) one `missing` node
      -- if (and only if) there was a parse error.
      -- We should not create an actual node of kind `k` in this case because it would mean we
      -- choose an "arbitrary" node (in practice the last one) in an alternative of the form
      -- `node k1 p1 <|> ... <|> node kn pn` when all parsers fail. With the code below we
      -- instead return a less misleading single `missing` node without randomly selecting any `ki`.
      let stack   := stack.push Syntax.missing
      ⟨stack, lhsPrec, pos, cache, err⟩
    else
      let newNode := Syntax.node k (stack.extract iniStackSz stack.size)
      let stack   := stack.shrink iniStackSz
      let stack   := stack.push newNode
      ⟨stack, lhsPrec, pos, cache, err⟩

def mkTrailingNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ =>
    let newNode := Syntax.node k (stack.extract (iniStackSz - 1) stack.size)
    let stack   := stack.shrink (iniStackSz - 1)
    let stack   := stack.push newNode
    ⟨stack, lhsPrec, pos, cache, err⟩

def setError (s : ParserState) (msg : String) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ => ⟨stack, lhsPrec, pos, cache, some { expected := [ msg ] }⟩

def mkError (s : ParserState) (msg : String) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { expected := [ msg ] }⟩

def mkUnexpectedError (s : ParserState) (msg : String) (expected : List String := []) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _⟩ => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { unexpected := msg, expected := expected }⟩

def mkEOIError (s : ParserState) (expected : List String := []) : ParserState :=
  s.mkUnexpectedError "unexpected end of input" expected

def mkErrorAt (s : ParserState) (msg : String) (pos : String.Pos) (initStackSz? : Option Nat := none) : ParserState :=
  match s,  initStackSz? with
  | ⟨stack, lhsPrec, _, cache, _⟩, none    => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { expected := [ msg ] }⟩
  | ⟨stack, lhsPrec, _, cache, _⟩, some sz => ⟨stack.shrink sz |>.push Syntax.missing, lhsPrec, pos, cache, some { expected := [ msg ] }⟩

def mkErrorsAt (s : ParserState) (ex : List String) (pos : String.Pos) (initStackSz? : Option Nat := none) : ParserState :=
  match s, initStackSz? with
  | ⟨stack, lhsPrec, _, cache, _⟩, none    => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { expected := ex }⟩
  | ⟨stack, lhsPrec, _, cache, _⟩, some sz => ⟨stack.shrink sz |>.push Syntax.missing, lhsPrec, pos, cache, some { expected := ex }⟩

def mkUnexpectedErrorAt (s : ParserState) (msg : String) (pos : String.Pos) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, _, cache, _⟩ => ⟨stack.push Syntax.missing, lhsPrec, pos, cache, some { unexpected := msg }⟩

end ParserState

def ParserFn := ParserContext → ParserState → ParserState

instance : Inhabited ParserFn where
  default := fun ctx s => s

inductive FirstTokens where
  | epsilon   : FirstTokens
  | unknown   : FirstTokens
  | tokens    : List Token → FirstTokens
  | optTokens : List Token → FirstTokens
  deriving Inhabited

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

instance : ToString FirstTokens := ⟨toStr⟩

end FirstTokens

structure ParserInfo where
  collectTokens : List Token → List Token := id
  collectKinds  : SyntaxNodeKindSet → SyntaxNodeKindSet := id
  firstTokens   : FirstTokens := FirstTokens.unknown
  deriving Inhabited

structure Parser where
  info : ParserInfo := {}
  fn   : ParserFn
  deriving Inhabited

abbrev TrailingParser := Parser

def dbgTraceStateFn (label : String) (p : ParserFn) : ParserFn :=
  fun c s =>
    let sz := s.stxStack.size
    let s' := p c s
    dbg_trace "{label}
  pos: {s'.pos}
  err: {s'.errorMsg}
  out: {s'.stxStack.extract sz s'.stxStack.size}" s'

def dbgTraceState (label : String) (p : Parser) : Parser where
  fn   := dbgTraceStateFn label p.fn
  info := p.info

@[noinline] def epsilonInfo : ParserInfo :=
  { firstTokens := FirstTokens.epsilon }

@[inline] def checkStackTopFn (p : Syntax → Bool) (msg : String) : ParserFn := fun c s =>
  if p s.stxStack.back then s
  else s.mkUnexpectedError msg

@[inline] def checkStackTop (p : Syntax → Bool) (msg : String) : Parser := {
  info := epsilonInfo,
  fn   := checkStackTopFn p msg
}

@[inline] def andthenFn (p q : ParserFn) : ParserFn := fun c s =>
  let s := p c s
  if s.hasError then s else q c s

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.seq q.firstTokens
}

@[inline] def andthen (p q : Parser) : Parser := {
  info := andthenInfo p.info q.info,
  fn   := andthenFn p.fn q.fn
}

instance : AndThen Parser where
  andThen a b := andthen a (b ())

@[inline] def nodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s     := p c s
  s.mkNode n iniSz

@[inline] def trailingNodeFn (n : SyntaxNodeKind) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stackSize
  let s     := p c s
  s.mkTrailingNode n iniSz

@[noinline] def nodeInfo (n : SyntaxNodeKind) (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens,
  collectKinds  := fun s => (p.collectKinds s).insert n,
  firstTokens   := p.firstTokens
}

@[inline] def node (n : SyntaxNodeKind) (p : Parser) : Parser := {
  info := nodeInfo n p.info,
  fn   := nodeFn n p.fn
}

def errorFn (msg : String) : ParserFn := fun _ s =>
  s.mkUnexpectedError msg

@[inline] def error (msg : String) : Parser := {
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

/- Generate an error at the position saved with the `withPosition` combinator.
   If `delta == true`, then it reports at saved position+1.
   This useful to make sure a parser consumed at least one character.  -/
@[inline] def errorAtSavedPos (msg : String) (delta : Bool) : Parser := {
  fn := errorAtSavedPosFn msg delta
}

/- Succeeds if `c.prec <= prec` -/
def checkPrecFn (prec : Nat) : ParserFn := fun c s =>
  if c.prec <= prec then s
  else s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def checkPrec (prec : Nat) : Parser := {
  info := epsilonInfo,
  fn   := checkPrecFn prec
}

/- Succeeds if `c.lhsPrec >= prec` -/
def checkLhsPrecFn (prec : Nat) : ParserFn := fun c s =>
  if s.lhsPrec >= prec then s
  else s.mkUnexpectedError "unexpected token at this precedence level; consider parenthesizing the term"

@[inline] def checkLhsPrec (prec : Nat) : Parser := {
  info := epsilonInfo,
  fn   := checkLhsPrecFn prec
}

def setLhsPrecFn (prec : Nat) : ParserFn := fun c s =>
  if s.hasError then s
  else { s with lhsPrec := prec }

@[inline] def setLhsPrec (prec : Nat) : Parser := {
  info := epsilonInfo,
  fn   := setLhsPrecFn prec
}

def checkInsideQuotFn : ParserFn := fun c s =>
  if c.quotDepth > 0 && !c.suppressInsideQuot then s
  else s.mkUnexpectedError "unexpected syntax outside syntax quotation"

@[inline] def checkInsideQuot : Parser := {
  info := epsilonInfo,
  fn   := checkInsideQuotFn
}

def checkOutsideQuotFn : ParserFn := fun c s =>
  if !c.quotDepth == 0 || c.suppressInsideQuot then s
  else s.mkUnexpectedError "unexpected syntax inside syntax quotation"

@[inline] def checkOutsideQuot : Parser := {
  info := epsilonInfo,
  fn   := checkOutsideQuotFn
}

def addQuotDepthFn (i : Int) (p : ParserFn) : ParserFn := fun c s =>
  p { c with quotDepth := c.quotDepth + i |>.toNat } s

@[inline] def incQuotDepth (p : Parser) : Parser := {
  info := p.info,
  fn   := addQuotDepthFn 1 p.fn
}

@[inline] def decQuotDepth (p : Parser) : Parser := {
  info := p.info,
  fn   := addQuotDepthFn (-1) p.fn
}

def suppressInsideQuotFn (p : ParserFn) : ParserFn := fun c s =>
  p { c with suppressInsideQuot := true } s

@[inline] def suppressInsideQuot (p : Parser) : Parser := {
  info := p.info,
  fn   := suppressInsideQuotFn p.fn
}

@[inline] def leadingNode (n : SyntaxNodeKind) (prec : Nat) (p : Parser) : Parser :=
  checkPrec prec >> node n p >> setLhsPrec prec

@[inline] def trailingNodeAux (n : SyntaxNodeKind) (p : Parser) : TrailingParser := {
  info := nodeInfo n p.info,
  fn   := trailingNodeFn n p.fn
}

@[inline] def trailingNode (n : SyntaxNodeKind) (prec lhsPrec : Nat) (p : Parser) : TrailingParser :=
  checkPrec prec >> checkLhsPrec lhsPrec >> trailingNodeAux n p >> setLhsPrec prec

def mergeOrElseErrors (s : ParserState) (error1 : Error) (iniPos : Nat) (mergeErrors : Bool) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, some error2⟩ =>
    if pos == iniPos then ⟨stack, lhsPrec, pos, cache, some (if mergeErrors then error1.merge error2 else error2)⟩
    else s
  | other => other

def orelseFnCore (p q : ParserFn) (mergeErrors : Bool) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  match s.errorMsg with
  | some errorMsg =>
    if s.pos == iniPos then
      mergeOrElseErrors (q c (s.restore iniSz iniPos)) errorMsg iniPos mergeErrors
    else
      s
  | none => s

@[inline] def orelseFn (p q : ParserFn) : ParserFn :=
  orelseFnCore p q true

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.merge q.firstTokens
}

/--
  Run `p`, falling back to `q` if `p` failed without consuming any input.

  NOTE: In order for the pretty printer to retrace an `orelse`, `p` must be a call to `node` or some other parser
  producing a single node kind. Nested `orelse` calls are flattened for this, i.e. `(node k1 p1 <|> node k2 p2) <|> ...`
  is fine as well. -/
@[inline] def orelse (p q : Parser) : Parser := {
  info := orelseInfo p.info q.info,
  fn   := orelseFn p.fn q.fn
}

instance : OrElse Parser where
  orElse a b := orelse a (b ())

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo := {
  collectTokens := info.collectTokens,
  collectKinds  := info.collectKinds
}

def atomicFn (p : ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  match p c s with
  | ⟨stack, lhsPrec, _, cache, some msg⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg⟩
  | other                       => other

@[inline] def atomic (p : Parser) : Parser := {
  info := p.info,
  fn   := atomicFn p.fn
}

def optionalFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s
  s.mkNode nullKind iniSz

@[noinline] def optionaInfo (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens,
  collectKinds  := p.collectKinds,
  firstTokens   := p.firstTokens.toOptional
}

@[inline] def optionalNoAntiquot (p : Parser) : Parser := {
  info := optionaInfo p.info,
  fn   := optionalFn p.fn
}

def lookaheadFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  if s.hasError then s else s.restore iniSz iniPos

@[inline] def lookahead (p : Parser) : Parser := {
  info := p.info,
  fn   := lookaheadFn p.fn
}

def notFollowedByFn (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := p c s
  if s.hasError then
    s.restore iniSz iniPos
  else
    let s := s.restore iniSz iniPos
    s.mkUnexpectedError s!"unexpected {msg}"

@[inline] def notFollowedBy (p : Parser) (msg : String) : Parser := {
  fn := notFollowedByFn p.fn msg
}

partial def manyAux (p : ParserFn) : ParserFn := fun c s => do
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

@[inline] def manyFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := manyAux p c s
  s.mkNode nullKind iniSz

@[inline] def manyNoAntiquot (p : Parser) : Parser := {
  info := noFirstTokenInfo p.info,
  fn   := manyFn p.fn
}

@[inline] def many1Fn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := andthenFn p (manyAux p) c s
  s.mkNode nullKind iniSz

@[inline] def many1NoAntiquot (p : Parser) : Parser := {
  info := p.info,
  fn   := many1Fn p.fn
}

private partial def sepByFnAux (p : ParserFn) (sep : ParserFn) (allowTrailingSep : Bool) (iniSz : Nat) (pOpt : Bool) : ParserFn :=
  let rec parse (pOpt : Bool) (c s) := do
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
  collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds
}

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds,
  firstTokens   := p.firstTokens
}

@[inline] def sepByNoAntiquot (p sep : Parser) (allowTrailingSep : Bool := false) : Parser := {
  info := sepByInfo p.info sep.info,
  fn   := sepByFn allowTrailingSep p.fn sep.fn
}

@[inline] def sepBy1NoAntiquot (p sep : Parser) (allowTrailingSep : Bool := false) : Parser := {
  info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn
}

/- Apply `f` to the syntax object produced by `p` -/
def withResultOfFn (p : ParserFn) (f : Syntax → Syntax) : ParserFn := fun c s =>
  let s := p c s
  if s.hasError then s
  else
    let stx := s.stxStack.back
    s.popSyntax.pushSyntax (f stx)

@[noinline] def withResultOfInfo (p : ParserInfo) : ParserInfo := {
  collectTokens := p.collectTokens,
  collectKinds  := p.collectKinds
}

@[inline] def withResultOf (p : Parser) (f : Syntax → Syntax) : Parser := {
  info := withResultOfInfo p.info,
  fn   := withResultOfFn p.fn f
}

@[inline] def many1Unbox (p : Parser) : Parser :=
  withResultOf (many1NoAntiquot p) fun stx => if stx.getNumArgs == 1 then stx.getArg 0 else stx

partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s.mkEOIError
  else if p (c.input.get i) then s.next c.input i
  else s.mkUnexpectedError errorMsg

partial def takeUntilFn (p : Char → Bool) : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s
  else if p (c.input.get i) then s
  else takeUntilFn p c (s.next c.input i)

def takeWhileFn (p : Char → Bool) : ParserFn :=
  takeUntilFn (fun c => !p c)

@[inline] def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : ParserFn :=
  andthenFn (satisfyFn p errorMsg) (takeWhileFn p)

partial def finishCommentBlock (nesting : Nat) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then eoi s
  else
    let curr := input.get i
    let i    := input.next i
    if curr == '-' then
      if input.atEnd i then eoi s
      else
        let curr := input.get i
        if curr == '/' then -- "-/" end of comment
          if nesting == 1 then s.next input i
          else finishCommentBlock (nesting-1) c (s.next input i)
        else
          finishCommentBlock nesting c (s.next input i)
    else if curr == '/' then
      if input.atEnd i then eoi s
      else
        let curr := input.get i
        if curr == '-' then finishCommentBlock (nesting+1) c (s.next input i)
        else finishCommentBlock nesting c (s.setPos i)
    else finishCommentBlock nesting c (s.setPos i)
where
  eoi s := s.mkUnexpectedError "unterminated comment"

/- Consume whitespace and comments -/
partial def whitespace : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s
  else
    let curr := input.get i
    if curr == '\t' then
      s.mkUnexpectedError "tabs are not allowed; please configure your editor to expand them"
    else if curr.isWhitespace then whitespace c (s.next input i)
    else if curr == '-' then
      let i    := input.next i
      let curr := input.get i
      if curr == '-' then andthenFn (takeUntilFn (fun c => c = '\n')) whitespace c (s.next input i)
      else s
    else if curr == '/' then
      let startPos := i
      let i        := input.next i
      let curr     := input.get i
      if curr == '-' then
        let i    := input.next i
        let curr := input.get i
        if curr == '-' || curr == '!' then s -- "/--" and "/-!" doc comment are actual tokens
        else andthenFn (finishCommentBlock 1) whitespace c (s.next input i)
      else s
    else s

def mkEmptySubstringAt (s : String) (p : Nat) : Substring :=
  { str := s, startPos := p, stopPos := p }

private def rawAux (startPos : Nat) (trailingWs : Bool) : ParserFn := fun c s =>
  let input   := c.input
  let stopPos := s.pos
  let leading := mkEmptySubstringAt input startPos
  let val     := input.extract startPos stopPos
  if trailingWs then
    let s        := whitespace c s
    let stopPos' := s.pos
    let trailing := { str := input, startPos := stopPos, stopPos := stopPos' : Substring }
    let atom     := mkAtom (SourceInfo.original leading startPos trailing (startPos + val.bsize)) val
    s.pushSyntax atom
  else
    let trailing := mkEmptySubstringAt input stopPos
    let atom     := mkAtom (SourceInfo.original leading startPos trailing (startPos + val.bsize)) val
    s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
@[inline] def rawFn (p : ParserFn) (trailingWs := false) : ParserFn := fun c s =>
  let startPos := s.pos
  let s := p c s
  if s.hasError then s else rawAux startPos trailingWs c s

@[inline] def chFn (c : Char) (trailingWs := false) : ParserFn :=
  rawFn (satisfyFn (fun d => c == d) ("'" ++ toString c ++ "'")) trailingWs

def rawCh (c : Char) (trailingWs := false) : Parser :=
  { fn := chFn c trailingWs }

def hexDigitFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i
    let i    := input.next i
    if curr.isDigit || ('a' <= curr && curr <= 'f') || ('A' <= curr && curr <= 'F') then s.setPos i
    else s.mkUnexpectedError "invalid hexadecimal numeral"

def quotedCharCoreFn (isQuotable : Char → Bool) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i
    if isQuotable curr then
      s.next input i
    else if curr == 'x' then
      andthenFn hexDigitFn hexDigitFn c (s.next input i)
    else if curr == 'u' then
      andthenFn hexDigitFn (andthenFn hexDigitFn (andthenFn hexDigitFn hexDigitFn)) c (s.next input i)
    else
      s.mkUnexpectedError "invalid escape sequence"

def isQuotableCharDefault (c : Char) : Bool :=
  c == '\\' || c == '\"' || c == '\'' || c == 'r' || c == 'n' || c == 't'

def quotedCharFn : ParserFn :=
  quotedCharCoreFn isQuotableCharDefault

/-- Push `(Syntax.node tk <new-atom>)` into syntax stack -/
def mkNodeToken (n : SyntaxNodeKind) (startPos : Nat) : ParserFn := fun c s =>
  let input     := c.input
  let stopPos   := s.pos
  let leading   := mkEmptySubstringAt input startPos
  let val       := input.extract startPos stopPos
  let s         := whitespace c s
  let wsStopPos := s.pos
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit n val info)

def charLitFnAux (startPos : Nat) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i
    let s    := s.setPos (input.next i)
    let s    := if curr == '\\' then quotedCharFn c s else s
    if s.hasError then s
    else
      let i    := s.pos
      let curr := input.get i
      let s    := s.setPos (input.next i)
      if curr == '\'' then mkNodeToken charLitKind startPos c s
      else s.mkUnexpectedError "missing end of character literal"

partial def strLitFnAux (startPos : Nat) : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkUnexpectedErrorAt "unterminated string literal" startPos
  else
    let curr := input.get i
    let s    := s.setPos (input.next i)
    if curr == '\"' then
      mkNodeToken strLitKind startPos c s
    else if curr == '\\' then andthenFn quotedCharFn (strLitFnAux startPos) c s
    else strLitFnAux startPos c s

def decimalNumberFn (startPos : Nat) (c : ParserContext) : ParserState → ParserState := fun s =>
  let s     := takeWhileFn (fun c => c.isDigit) c s
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '.' || curr == 'e' || curr == 'E' then
    let s := parseOptDot s
    let s := parseOptExp s
    mkNodeToken scientificLitKind startPos c s
  else
    mkNodeToken numLitKind startPos c s
where
  parseOptDot s :=
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

  parseOptExp s :=
    let input := c.input
    let i     := s.pos
    let curr  := input.get i
    if curr == 'e' || curr == 'E' then
      let i    := input.next i
      let i    := if input.get i == '-' then input.next i else i
      let curr := input.get i
      if curr.isDigit then
        takeWhileFn (fun c => c.isDigit) c (s.setPos i)
      else
        s.setPos i
    else
      s

def binNumberFn (startPos : Nat) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "binary number" c s
  mkNodeToken numLitKind startPos c s

def octalNumberFn (startPos : Nat) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "octal number" c s
  mkNodeToken numLitKind startPos c s

def hexNumberFn (startPos : Nat) : ParserFn := fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" c s
  mkNodeToken numLitKind startPos c s

def numberFnAux : ParserFn := fun c s =>
  let input    := c.input
  let startPos := s.pos
  if input.atEnd startPos then s.mkEOIError
  else
    let curr := input.get startPos
    if curr == '0' then
      let i    := input.next startPos
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

private def isToken (idStartPos idStopPos : Nat) (tk : Option Token) : Bool :=
  match tk with
  | none    => false
  | some tk =>
     -- if a token is both a symbol and a valid identifier (i.e. a keyword),
     -- we want it to be recognized as a symbol
    tk.bsize ≥ idStopPos - idStartPos


def mkTokenAndFixPos (startPos : Nat) (tk : Option Token) : ParserFn := fun c s =>
  match tk with
  | none    => s.mkErrorAt "token" startPos
  | some tk =>
    if c.forbiddenTk? == some tk then
      s.mkErrorAt "forbidden token" startPos
    else
      let input     := c.input
      let leading   := mkEmptySubstringAt input startPos
      let stopPos   := startPos + tk.bsize
      let s         := s.setPos stopPos
      let s         := whitespace c s
      let wsStopPos := s.pos
      let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
      let atom      := mkAtom (SourceInfo.original leading startPos trailing stopPos) tk
      s.pushSyntax atom

def mkIdResult (startPos : Nat) (tk : Option Token) (val : Name) : ParserFn := fun c s =>
  let stopPos           := s.pos
  if isToken startPos stopPos tk then
    mkTokenAndFixPos startPos tk c s
  else
    let input           := c.input
    let rawVal          := { str := input, startPos := startPos, stopPos := stopPos  : Substring }
    let s               := whitespace c s
    let trailingStopPos := s.pos
    let leading         := mkEmptySubstringAt input startPos
    let trailing        := { str := input, startPos := stopPos, stopPos := trailingStopPos : Substring }
    let info            := SourceInfo.original leading startPos trailing stopPos
    let atom            := mkIdent info rawVal val
    s.pushSyntax atom

partial def identFnAux (startPos : Nat) (tk : Option Token) (r : Name) : ParserFn :=
  let rec parse (r : Name) (c s) := do
    let input := c.input
    let i     := s.pos
    if input.atEnd i then
      return s.mkEOIError
    let curr := input.get i
    if isIdBeginEscape curr then
      let startPart := input.next i
      let s         := takeUntilFn isIdEndEscape c (s.setPos startPart)
      if input.atEnd s.pos then
        return s.mkUnexpectedErrorAt "unterminated identifier escape" startPart
      let stopPart  := s.pos
      let s         := s.next c.input s.pos
      let r := Name.mkStr r (input.extract startPart stopPart)
      if isIdCont input s then
        let s := s.next input s.pos
        parse r c s
      else
        mkIdResult startPos tk r c s
    else if isIdFirst curr then
      let startPart := i
      let s         := takeWhileFn isIdRest c (s.next input i)
      let stopPart  := s.pos
      let r := Name.mkStr r (input.extract startPart stopPart)
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

private def nameLitAux (startPos : Nat) : ParserFn := fun c s =>
  let input := c.input
  let s     := identFnAux startPos none Name.anonymous c (s.next input startPos)
  if s.hasError then
    s
  else
    let stx := s.stxStack.back
    match stx with
    | Syntax.ident info rawStr _ _ =>
      let s := s.popSyntax
      s.pushSyntax (Syntax.mkNameLit rawStr.toString info)
    | _ => s.mkError "invalid Name literal"

private def tokenFnAux : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  let curr  := input.get i
  if curr == '\"' then
    strLitFnAux i c (s.next input i)
  else if curr == '\'' then
    charLitFnAux i c (s.next input i)
  else if curr.isDigit then
    numberFnAux c s
  else if curr == '`' && isIdFirstOrBeginEscape (getNext input i) then
    nameLitAux i c s
  else
    let (_, tk) := c.tokens.matchPrefix input i
    identFnAux i tk Name.anonymous c s

private def updateCache (startPos : Nat) (s : ParserState) : ParserState :=
  -- do not cache token parsing errors, which are rare and usually fatal and thus not worth an extra field in `TokenCache`
  match s with
  | ⟨stack, lhsPrec, pos, cache, none⟩ =>
    if stack.size == 0 then s
    else
      let tk := stack.back
      ⟨stack, lhsPrec, pos, { tokenCache := { startPos := startPos, stopPos := pos, token := tk } }, none⟩
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
      let s := tokenFnAux c s
      updateCache i s

def peekTokenAux (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn [] c s
  if let some e := s.errorMsg then (s.restore iniSz iniPos, Except.error s)
  else
    let stx := s.stxStack.back
    (s.restore iniSz iniPos, Except.ok stx)

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Except ParserState Syntax :=
  let tkc := s.cache.tokenCache
  if tkc.startPos == s.pos then
    (s, Except.ok tkc.token)
  else
    peekTokenAux c s

/- Treat keywords as identifiers. -/
def rawIdentFn : ParserFn := fun c s =>
  let input := c.input
  let i     := s.pos
  if input.atEnd i then s.mkEOIError
  else identFnAux i none Name.anonymous c s

@[inline] def satisfySymbolFn (p : String → Bool) (expected : List String) : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let startPos := s.pos
  let s        := tokenFn expected c s
  if s.hasError then
    s
  else
    match s.stxStack.back with
    | Syntax.atom _ sym => if p sym then s else s.mkErrorsAt expected startPos initStackSz
    | _                 => s.mkErrorsAt expected startPos initStackSz

def symbolFnAux (sym : String) (errorMsg : String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolInfo (sym : String) : ParserInfo := {
  collectTokens := fun tks => sym :: tks,
  firstTokens   := FirstTokens.tokens [ sym ]
}

@[inline] def symbolFn (sym : String) : ParserFn :=
  symbolFnAux sym ("'" ++ sym ++ "'")

@[inline] def symbolNoAntiquot (sym : String) : Parser :=
  let sym := sym.trim
  { info := symbolInfo sym,
    fn   := symbolFn sym }

def checkTailNoWs (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | SourceInfo.original _ _ trailing _ => trailing.stopPos == trailing.startPos
  | _                                  => false

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
    | Syntax.atom _ sym' =>
      if sym == sym' then s else s.mkErrorAt errorMsg startPos initStackSz
    | Syntax.ident info rawVal _ _ =>
      if sym == rawVal.toString then
        let s := s.popSyntax
        s.pushSyntax (Syntax.atom info sym)
      else
        s.mkErrorAt errorMsg startPos initStackSz
    | _ => s.mkErrorAt errorMsg startPos initStackSz

@[inline] def nonReservedSymbolFn (sym : String) : ParserFn :=
  nonReservedSymbolFnAux sym ("'" ++ sym ++ "'")

def nonReservedSymbolInfo (sym : String) (includeIdent : Bool) : ParserInfo := {
  firstTokens  :=
    if includeIdent then
      FirstTokens.tokens [ sym, "ident" ]
    else
      FirstTokens.tokens [ sym ]
}

@[inline] def nonReservedSymbolNoAntiquot (sym : String) (includeIdent := false) : Parser :=
  let sym := sym.trim
  { info := nonReservedSymbolInfo sym includeIdent,
    fn   := nonReservedSymbolFn sym }

partial def strAux (sym : String) (errorMsg : String) (j : Nat) :ParserFn :=
  let rec parse (j c s) :=
    if sym.atEnd j then s
    else
      let i := s.pos
      let input := c.input
      if input.atEnd i || sym.get j != input.get i then s.mkError errorMsg
      else parse (sym.next j) c (s.next input i)
  parse j

def checkTailWs (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | SourceInfo.original _ _ trailing _ => trailing.stopPos > trailing.startPos
  | _                                  => false

def checkWsBeforeFn (errorMsg : String) : ParserFn := fun c s =>
  let prev := s.stxStack.back
  if checkTailWs prev then s else s.mkError errorMsg

def checkWsBefore (errorMsg : String := "space before") : Parser := {
  info := epsilonInfo,
  fn   := checkWsBeforeFn errorMsg
}

def checkTailLinebreak (prev : Syntax) : Bool :=
  match prev.getTailInfo with
  | SourceInfo.original _ _ trailing _ => trailing.contains '\n'
  | _ => false

def checkLinebreakBeforeFn (errorMsg : String) : ParserFn := fun c s =>
  let prev := s.stxStack.back
  if checkTailLinebreak prev then s else s.mkError errorMsg

def checkLinebreakBefore (errorMsg : String := "line break") : Parser := {
  info := epsilonInfo
  fn   := checkLinebreakBeforeFn errorMsg
}

private def pickNonNone (stack : Array Syntax) : Syntax :=
  match stack.findRev? $ fun stx => !stx.isNone with
  | none => Syntax.missing
  | some stx => stx

def checkNoWsBeforeFn (errorMsg : String) : ParserFn := fun c s =>
  let prev := pickNonNone s.stxStack
  if checkTailNoWs prev then s else s.mkError errorMsg

def checkNoWsBefore (errorMsg : String := "no space before") : Parser := {
  info := epsilonInfo,
  fn   := checkNoWsBeforeFn errorMsg
}

def unicodeSymbolFnAux (sym asciiSym : String) (expected : List String) : ParserFn :=
  satisfySymbolFn (fun s => s == sym || s == asciiSym) expected

def unicodeSymbolInfo (sym asciiSym : String) : ParserInfo := {
  collectTokens := fun tks => sym :: asciiSym :: tks,
  firstTokens   := FirstTokens.tokens [ sym, asciiSym ]
}

@[inline] def unicodeSymbolFn (sym asciiSym : String) : ParserFn :=
  unicodeSymbolFnAux sym asciiSym ["'" ++ sym ++ "', '" ++ asciiSym ++ "'"]

@[inline] def unicodeSymbolNoAntiquot (sym asciiSym : String) : Parser :=
  let sym := sym.trim
  let asciiSym := asciiSym.trim
  { info := unicodeSymbolInfo sym asciiSym,
    fn   := unicodeSymbolFn sym asciiSym }

def mkAtomicInfo (k : String) : ParserInfo :=
  { firstTokens := FirstTokens.tokens [ k ] }

def numLitFn : ParserFn :=
  fun c s =>
    let initStackSz := s.stackSize
    let iniPos := s.pos
    let s      := tokenFn ["numeral"] c s
    if !s.hasError && !(s.stxStack.back.isOfKind numLitKind) then s.mkErrorAt "numeral" iniPos initStackSz else s

@[inline] def numLitNoAntiquot : Parser := {
  fn   := numLitFn,
  info := mkAtomicInfo "numLit"
}

def scientificLitFn : ParserFn :=
  fun c s =>
    let initStackSz := s.stackSize
    let iniPos := s.pos
    let s      := tokenFn ["scientific number"] c s
    if !s.hasError && !(s.stxStack.back.isOfKind scientificLitKind) then s.mkErrorAt "scientific number" iniPos initStackSz else s

@[inline] def scientificLitNoAntiquot : Parser := {
  fn   := scientificLitFn,
  info := mkAtomicInfo "scientificLit"
}

def strLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["string literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "string literal" iniPos initStackSz else s

@[inline] def strLitNoAntiquot : Parser := {
  fn   := strLitFn,
  info := mkAtomicInfo "strLit"
}

def charLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["char literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind charLitKind) then s.mkErrorAt "character literal" iniPos initStackSz else s

@[inline] def charLitNoAntiquot : Parser := {
  fn   := charLitFn,
  info := mkAtomicInfo "charLit"
}

def nameLitFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s := tokenFn ["Name literal"] c s
  if !s.hasError && !(s.stxStack.back.isOfKind nameLitKind) then s.mkErrorAt "Name literal" iniPos initStackSz else s

@[inline] def nameLitNoAntiquot : Parser := {
  fn   := nameLitFn,
  info := mkAtomicInfo "nameLit"
}

def identFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["identifier"] c s
  if !s.hasError && !(s.stxStack.back.isIdent) then s.mkErrorAt "identifier" iniPos initStackSz else s

@[inline] def identNoAntiquot : Parser := {
  fn   := identFn,
  info := mkAtomicInfo "ident"
}

@[inline] def rawIdentNoAntiquot : Parser := {
  fn := rawIdentFn
}

def identEqFn (id : Name) : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let s      := tokenFn ["identifier"] c s
  if s.hasError then
    s
  else match s.stxStack.back with
    | Syntax.ident _ _ val _ => if val != id then s.mkErrorAt ("expected identifier '" ++ toString id ++ "'") iniPos initStackSz else s
    | _ => s.mkErrorAt "identifier" iniPos initStackSz

@[inline] def identEq (id : Name) : Parser := {
  fn   := identEqFn id,
  info := mkAtomicInfo "ident"
}

namespace ParserState

def keepTop (s : Array Syntax) (startStackSize : Nat) : Array Syntax :=
  let node  := s.back
  s.shrink startStackSize |>.push node

def keepNewError (s : ParserState) (oldStackSize : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err⟩ => ⟨keepTop stack oldStackSize, lhsPrec, pos, cache, err⟩

def keepPrevError (s : ParserState) (oldStackSize : Nat) (oldStopPos : String.Pos) (oldError : Option Error) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, _, cache, _⟩ => ⟨stack.shrink oldStackSize, lhsPrec, oldStopPos, cache, oldError⟩

def mergeErrors (s : ParserState) (oldStackSize : Nat) (oldError : Error) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, some err⟩ =>
    if oldError == err then s
    else ⟨stack.shrink oldStackSize, lhsPrec, pos, cache, some (oldError.merge err)⟩
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
def runLongestMatchParser (left? : Option Syntax) (startLhsPrec : Nat) (p : ParserFn) : ParserFn := fun c s => do
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
  let prevErrorMsg  := s.errorMsg
  let prevStopPos   := s.pos
  let prevSize      := s.stackSize
  let prevLhsPrec   := s.lhsPrec
  let s             := s.restore prevSize startPos
  let s             := runLongestMatchParser left? startLhsPrec p c s
  match prevErrorMsg, s.errorMsg with
  | none, none   => -- both succeeded
    if s.pos > prevStopPos || (s.pos == prevStopPos && prio > prevPrio)      then (s.replaceLongest startSize, prio)
    else if s.pos < prevStopPos || (s.pos == prevStopPos && prio < prevPrio) then ({ s.restore prevSize prevStopPos with lhsPrec := prevLhsPrec }, prevPrio) -- keep prev
    -- it is not clear what the precedence of a choice node should be, so we conservatively take the minimum
    else ({s with lhsPrec := s.lhsPrec.min prevLhsPrec }, prio)
  | none, some _ => -- prev succeeded, current failed
    ({ s.restore prevSize prevStopPos with lhsPrec := prevLhsPrec }, prevPrio)
  | some oldError, some _ => -- both failed
    if s.pos > prevStopPos || (s.pos == prevStopPos && prio > prevPrio)      then (s.keepNewError startSize, prio)
    else if s.pos < prevStopPos || (s.pos == prevStopPos && prio < prevPrio) then (s.keepPrevError prevSize prevStopPos prevErrorMsg, prevPrio)
    else (s.mergeErrors prevSize oldError, prio)
  | some _, none => -- prev failed, current succeeded
    let successNode := s.stxStack.back
    let s           := s.shrinkStack startSize -- restore stack to initial size to make sure (failure) nodes are removed from the stack
    (s.pushSyntax successNode, prio) -- put successNode back on the stack

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
  if !s.hasError && s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

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

@[inline] def checkColGeFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.column ≥ savedPos.column then s
    else s.mkError errorMsg

@[inline] def checkColGe (errorMsg : String := "checkColGe") : Parser :=
  { fn := checkColGeFn errorMsg }

@[inline] def checkColGtFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.column > savedPos.column then s
    else s.mkError errorMsg

@[inline] def checkColGt (errorMsg : String := "checkColGt") : Parser :=
  { fn := checkColGtFn errorMsg }

@[inline] def checkLineEqFn (errorMsg : String) : ParserFn := fun c s =>
  match c.savedPos? with
  | none => s
  | some savedPos =>
    let savedPos := c.fileMap.toPosition savedPos
    let pos      := c.fileMap.toPosition s.pos
    if pos.line == savedPos.line then s
    else s.mkError errorMsg

@[inline] def checkLineEq (errorMsg : String := "checkLineEq") : Parser :=
  { fn := checkLineEqFn errorMsg }

@[inline] def withPosition (p : Parser) : Parser := {
  info := p.info,
  fn   := fun c s =>
    p.fn { c with savedPos? := s.pos } s
}

@[inline] def withoutPosition (p : Parser) : Parser := {
  info := p.info,
  fn   := fun c s =>
    let pos := c.fileMap.toPosition s.pos
    p.fn { c with savedPos? := none } s
}

@[inline] def withForbidden (tk : Token) (p : Parser) : Parser := {
  info := p.info,
  fn   := fun c s => p.fn { c with forbiddenTk? := tk } s
}

@[inline] def withoutForbidden (p : Parser) : Parser := {
  info := p.info,
  fn   := fun c s => p.fn { c with forbiddenTk? := none } s
}

def eoiFn : ParserFn := fun c s =>
  let i := s.pos
  if c.input.atEnd i then s
  else s.mkError "expected end of file"

@[inline] def eoi : Parser :=
  { fn := eoiFn }

open Std (RBMap RBMap.empty)

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickCmp

namespace TokenMap

def insert (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
  match map.find? k with
  | none    => Std.RBMap.insert map k [v]
  | some vs => Std.RBMap.insert map k (v::vs)

instance : Inhabited (TokenMap α) := ⟨RBMap.empty⟩

instance : EmptyCollection (TokenMap α) := ⟨RBMap.empty⟩

end TokenMap

structure PrattParsingTables where
  leadingTable    : TokenMap (Parser × Nat) := {}
  leadingParsers  : List (Parser × Nat) := [] -- for supporting parsers we cannot obtain first token
  trailingTable   : TokenMap (Parser × Nat) := {}
  trailingParsers : List (Parser × Nat) := [] -- for supporting parsers such as function application

instance : Inhabited PrattParsingTables := ⟨{}⟩

/-
  The type `leadingIdentBehavior` specifies how the parsing table
  lookup function behaves for identifiers.  The function `prattParser`
  uses two tables `leadingTable` and `trailingTable`. They map tokens
  to parsers.

  - `LeadingIdentBehavior.default`: if the leading token
    is an identifier, then `prattParser` just executes the parsers
    associated with the auxiliary token "ident".

  - `LeadingIdentBehavior.symbol`: if the leading token is
    an identifier `<foo>`, and there are parsers `P` associated with
    the toek `<foo>`, then it executes `P`. Otherwise, it executes
    only the parsers associated with the auxiliary token "ident".

  - `LeadingIdentBehavior.both`: if the leading token
    an identifier `<foo>`, the it executes the parsers associated
    with token `<foo>` and parsers associated with the auxiliary
    token "ident".

  We use `LeadingIdentBehavior.symbol` and `LeadingIdentBehavior.both`
  and `nonReservedSymbol` parser to implement the `tactic` parsers.
  The idea is to avoid creating a reserved symbol for each
  builtin tactic (e.g., `apply`, `assumption`, etc.).  That is, users
  may still use these symbols as identifiers (e.g., naming a
  function).
-/

inductive LeadingIdentBehavior where
  | default
  | symbol
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
  tables   : PrattParsingTables
  behavior : LeadingIdentBehavior
  deriving Inhabited

abbrev ParserCategories := Std.PersistentHashMap Name ParserCategory

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (behavior : LeadingIdentBehavior) : ParserState × List α :=
  let (s, stx) := peekToken c s
  let find (n : Name) : ParserState × List α :=
    match map.find? n with
    | some as => (s, as)
    | _       => (s, [])
  match stx with
  | Except.ok (Syntax.atom _ sym)      => find (Name.mkSimple sym)
  | Except.ok (Syntax.ident _ _ val _) =>
    match behavior with
    | LeadingIdentBehavior.default => find identKind
    | LeadingIdentBehavior.symbol =>
      match map.find? val with
      | some as => (s, as)
      | none    => find identKind
    | LeadingIdentBehavior.both =>
      match map.find? val with
      | some as => match map.find? identKind with
        | some as' => (s, as ++ as')
        | _        => (s, as)
      | none    => find identKind
  | Except.ok (Syntax.node k _)        => find k
  | Except.ok _                        => (s, [])
  | Except.error s'                    => (s', [])

abbrev CategoryParserFn := Name → ParserFn

builtin_initialize categoryParserFnRef : IO.Ref CategoryParserFn ← IO.mkRef fun _ => whitespace

builtin_initialize categoryParserFnExtension : EnvExtension CategoryParserFn ← registerEnvExtension $ categoryParserFnRef.get

def categoryParserFn (catName : Name) : ParserFn := fun ctx s =>
  categoryParserFnExtension.getState ctx.env catName ctx s

def categoryParser (catName : Name) (prec : Nat) : Parser := {
  fn := fun c s => categoryParserFn catName { c with prec := prec } s
}

-- Define `termParser` here because we need it for antiquotations
@[inline] def termParser (prec : Nat := 0) : Parser :=
  categoryParser `term prec

/- ============== -/
/- Antiquotations -/
/- ============== -/

/-- Fail if previous token is immediately followed by ':'. -/
def checkNoImmediateColon : Parser := {
  fn := fun c s =>
    let prev := s.stxStack.back
    if checkTailNoWs prev then
      let input := c.input
      let i     := s.pos
      if input.atEnd i then s
      else
        let curr := input.get i
        if curr == ':' then
          s.mkUnexpectedError "unexpected ':'"
        else s
    else s
}

def setExpectedFn (expected : List String) (p : ParserFn) : ParserFn := fun c s =>
  match p c s with
    | s'@{ errorMsg := some msg, .. } => { s' with errorMsg := some { msg with expected := [] } }
    | s'                              => s'

def setExpected (expected : List String) (p : Parser) : Parser :=
  { fn := setExpectedFn expected p.fn, info := p.info }

def pushNone : Parser :=
  { fn := fun c s => s.pushSyntax mkNullNode }

-- We support two kinds of antiquotations: `$id` and `$(t)`, where `id` is a term identifier and `t` is a term.
def antiquotNestedExpr : Parser := node `antiquotNestedExpr (symbolNoAntiquot "(" >> decQuotDepth termParser >> symbolNoAntiquot ")")
def antiquotExpr : Parser       := identNoAntiquot <|> antiquotNestedExpr

@[inline] def tokenWithAntiquotFn (p : ParserFn) : ParserFn := fun c s => do
  let s := p c s
  if s.hasError || c.quotDepth == 0 then
    return s
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := (checkNoWsBefore >> symbolNoAntiquot "%" >> symbolNoAntiquot "$" >> checkNoWsBefore >> antiquotExpr).fn c s
  if s.hasError then
    return s.restore iniSz iniPos
  s.mkNode (`token_antiquot) (iniSz - 1)

@[inline] def tokenWithAntiquot (p : Parser) : Parser where
  fn   := tokenWithAntiquotFn p.fn
  info := p.info

@[inline] def symbol (sym : String) : Parser :=
  tokenWithAntiquot (symbolNoAntiquot sym)

instance : Coe String Parser := ⟨fun s => symbol s ⟩

@[inline] def nonReservedSymbol (sym : String) (includeIdent := false) : Parser :=
  tokenWithAntiquot (nonReservedSymbolNoAntiquot sym includeIdent)

@[inline] def unicodeSymbol (sym asciiSym : String) : Parser :=
  tokenWithAntiquot (unicodeSymbolNoAntiquot sym asciiSym)

/--
  Define parser for `$e` (if anonymous == true) and `$e:name`. Both
  forms can also be used with an appended `*` to turn them into an
  antiquotation "splice". If `kind` is given, it will additionally be checked
  when evaluating `match_syntax`. Antiquotations can be escaped as in `$$e`, which
  produces the syntax tree for `$e`. -/
def mkAntiquot (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parser :=
  let kind := (kind.getD Name.anonymous) ++ `antiquot
  let nameP := node `antiquotName $ checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbol ":" >> nonReservedSymbol name
  -- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
  -- antiquotation kind via `noImmediateColon`
  let nameP := if anonymous then nameP <|> checkNoImmediateColon >> pushNone else nameP
  -- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
  leadingNode kind maxPrec $ atomic $
    setExpected [] "$" >>
    manyNoAntiquot (checkNoWsBefore "" >> "$") >>
    checkNoWsBefore "no space before spliced term" >> antiquotExpr >>
    nameP

def tryAnti (c : ParserContext) (s : ParserState) : Bool := do
  if c.quotDepth == 0 then
    return false
  let (s, stx) := peekToken c s
  match stx with
  | Except.ok stx@(Syntax.atom _ sym) => sym == "$"
  | _                                 => false

@[inline] def withAntiquotFn (antiquotP p : ParserFn) : ParserFn := fun c s =>
  if tryAnti c s then orelseFn antiquotP p c s else p c s

/-- Optimized version of `mkAntiquot ... <|> p`. -/
@[inline] def withAntiquot (antiquotP p : Parser) : Parser := {
  fn := withAntiquotFn antiquotP.fn p.fn,
  info := orelseInfo antiquotP.info p.info
}

def withoutInfo (p : Parser) : Parser :=
  { fn := p.fn }

/-- Parse `$[p]suffix`, e.g. `$[p],*`. -/
def mkAntiquotSplice (kind : SyntaxNodeKind) (p suffix : Parser) : Parser :=
  let kind := kind ++ `antiquot_scope
  leadingNode kind maxPrec $ atomic $
    setExpected [] "$" >>
    manyNoAntiquot (checkNoWsBefore "" >> "$") >>
    checkNoWsBefore "no space before spliced term" >> symbol "[" >> node nullKind p >> symbol "]" >>
    suffix

@[inline] def withAntiquotSuffixSpliceFn (kind : SyntaxNodeKind) (p suffix : ParserFn) : ParserFn := fun c s => do
  let s := p c s
  if s.hasError || c.quotDepth == 0 || !s.stxStack.back.isAntiquot then
    return s
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s      := suffix c s
  if s.hasError then
    return s.restore iniSz iniPos
  s.mkNode (kind ++ `antiquot_suffix_splice) (s.stxStack.size - 2)

/-- Parse `suffix` after an antiquotation, e.g. `$x,*`, and put both into a new node. -/
@[inline] def withAntiquotSuffixSplice (kind : SyntaxNodeKind) (p suffix : Parser) : Parser := {
  info := andthenInfo p.info suffix.info,
  fn   := withAntiquotSuffixSpliceFn kind p.fn suffix.fn
}

def withAntiquotSpliceAndSuffix (kind : SyntaxNodeKind) (p suffix : Parser) :=
  -- prevent `p`'s info from being collected twice
  withAntiquot (mkAntiquotSplice kind (withoutInfo p) suffix) (withAntiquotSuffixSplice kind p suffix)

def nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : Parser) (anonymous := false) : Parser :=
  withAntiquot (mkAntiquot name kind anonymous) $ node kind p

/- ===================== -/
/- End of Antiquotations -/
/- ===================== -/

def sepByElemParser (p : Parser) (sep : String) : Parser :=
  withAntiquotSpliceAndSuffix `sepBy p (symbol (sep.trim ++ "*"))

def sepBy (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepByNoAntiquot (sepByElemParser p sep) psep allowTrailingSep

def sepBy1 (p : Parser) (sep : String) (psep : Parser := symbol sep) (allowTrailingSep : Bool := false) : Parser :=
  sepBy1NoAntiquot (sepByElemParser p sep) psep allowTrailingSep

def categoryParserOfStackFn (offset : Nat) : ParserFn := fun ctx s =>
  let stack := s.stxStack
  if stack.size < offset + 1 then
    s.mkUnexpectedError ("failed to determine parser category using syntax stack, stack is too small")
  else
    match stack.get! (stack.size - offset - 1) with
    | Syntax.ident _ _ catName _ => categoryParserFn catName ctx s
    | _ => s.mkUnexpectedError ("failed to determine parser category using syntax stack, the specified element on the stack is not an identifier")

def categoryParserOfStack (offset : Nat) (prec : Nat := 0) : Parser :=
  { fn := fun c s => categoryParserOfStackFn offset { c with prec := prec } s }

unsafe def evalParserConstUnsafe (declName : Name) : ParserFn := fun ctx s =>
  match ctx.env.evalConstCheck Parser ctx.options `Lean.Parser.Parser declName <|>
        ctx.env.evalConstCheck Parser ctx.options `Lean.Parser.TrailingParser declName with
  | Except.ok p    => p.fn ctx s
  | Except.error e => s.mkUnexpectedError s!"error running parser {declName}: {e}"

@[implementedBy evalParserConstUnsafe]
constant evalParserConst (declName : Name) : ParserFn

unsafe def parserOfStackFnUnsafe (offset : Nat) : ParserFn := fun ctx s =>
  let stack := s.stxStack
  if stack.size < offset + 1 then
    s.mkUnexpectedError ("failed to determine parser using syntax stack, stack is too small")
  else
    match stack.get! (stack.size - offset - 1) with
    | Syntax.ident (val := parserName) .. =>
      match ctx.resolveName parserName with
      | [(parserName, [])] =>
        let iniSz := s.stackSize
        let s := evalParserConst parserName ctx s
        if !s.hasError && s.stackSize != iniSz + 1 then
          s.mkUnexpectedError "expected parser to return exactly one syntax object"
        else
          s
      | _::_::_ => s.mkUnexpectedError s!"ambiguous parser name {parserName}"
      | _ => s.mkUnexpectedError s!"unknown parser {parserName}"
    | _ => s.mkUnexpectedError ("failed to determine parser using syntax stack, the specified element on the stack is not an identifier")

@[implementedBy parserOfStackFnUnsafe]
constant parserOfStackFn (offset : Nat) : ParserFn

def parserOfStack (offset : Nat) (prec : Nat := 0) : Parser :=
  { fn := fun c s => parserOfStackFn offset { c with prec := prec } s }

register_builtin_option internal.parseQuotWithCurrentStage : Bool := {
  defValue := false
  group    := "internal"
  descr    := "(Lean bootstrapping) use parsers from the current stage inside quotations"
}

/-- Run `declName` if possible and inside a quotation, or else `p`. The `ParserInfo` will always be taken from `p`. -/
def evalInsideQuot (declName : Name) (p : Parser) : Parser := { p with
  fn := fun c s =>
    if c.quotDepth > 0 && !c.suppressInsideQuot && internal.parseQuotWithCurrentStage.get c.options && c.env.contains declName then
      evalParserConst declName c s
    else
      p.fn c s }

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
  if s.stackSize == iniSz + 1 then s
  else s.mkNode nullKind iniSz -- throw error instead?

def leadingParserAux (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) : ParserFn := fun c s => do
  let iniSz   := s.stackSize
  let (s, ps) := indexed tables.leadingTable c s behavior
  if s.hasError then
    return s
  let ps      := tables.leadingParsers ++ ps
  if ps.isEmpty then
    return s.mkError (toString kind)
  let s := longestMatchFn none ps c s
  mkResult s iniSz

@[inline] def leadingParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn :=
  withAntiquotFn antiquotParser (leadingParserAux kind tables behavior)

def trailingLoopStep (tables : PrattParsingTables) (left : Syntax) (ps : List (Parser × Nat)) : ParserFn := fun c s =>
  longestMatchFn left (ps ++ tables.trailingParsers) c s

partial def trailingLoop (tables : PrattParsingTables) (c : ParserContext) (s : ParserState) : ParserState := do
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
@[inline] def prattParser (kind : Name) (tables : PrattParsingTables) (behavior : LeadingIdentBehavior) (antiquotParser : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s := leadingParser kind tables behavior antiquotParser c s
  if s.hasError then
    s
  else
    trailingLoop tables c s

def fieldIdxFn : ParserFn := fun c s =>
  let initStackSz := s.stackSize
  let iniPos := s.pos
  let curr     := c.input.get iniPos
  if curr.isDigit && curr != '0' then
    let s     := takeWhileFn (fun c => c.isDigit) c s
    mkNodeToken fieldIdxKind iniPos c s
  else
    s.mkErrorAt "field index" iniPos initStackSz

@[inline] def fieldIdx : Parser :=
  withAntiquot (mkAntiquot "fieldIdx" `fieldIdx) {
    fn   := fieldIdxFn,
    info := mkAtomicInfo "fieldIdx"
  }

@[inline] def skip : Parser := {
  fn   := fun c s => s,
  info := epsilonInfo
}

end Parser

namespace Syntax

section
variable {β : Type} {m : Type → Type} [Monad m]

@[inline] def foldArgsM (s : Syntax) (f : Syntax → β → m β) (b : β) : m β :=
  s.getArgs.foldlM (flip f) b

@[inline] def foldArgs (s : Syntax) (f : Syntax → β → β) (b : β) : β :=
  Id.run (s.foldArgsM f b)

@[inline] def forArgsM (s : Syntax) (f : Syntax → m Unit) : m Unit :=
  s.foldArgsM (fun s _ => f s) ()
end

end Syntax
end Lean
