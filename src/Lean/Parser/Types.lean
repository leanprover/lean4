/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Data.Trie
import Lean.Syntax
import Lean.Message
import Lean.DocString.Extension

namespace Lean.Parser

abbrev mkAtom (info : SourceInfo) (val : String) : Syntax :=
  Syntax.atom info val

abbrev mkIdent (info : SourceInfo) (rawVal : Substring) (val : Name) : Syntax :=
  Syntax.ident info rawVal val []

/-- Return character after position `pos` -/
def getNext (input : String) (pos : String.Pos) : Char :=
  input.get (input.next pos)

/-- Maximal (and function application) precedence.
   In the standard lean language, no parser has precedence higher than `maxPrec`.

   Note that nothing prevents users from using a higher precedence, but we strongly
   discourage them from doing it. -/
def maxPrec  : Nat := eval_prec max
def argPrec  : Nat := eval_prec arg
def leadPrec : Nat := eval_prec lead
def minPrec  : Nat := eval_prec min

abbrev Token := String

abbrev TokenTable := Lean.Data.Trie Token

abbrev SyntaxNodeKindSet := PersistentHashMap SyntaxNodeKind Unit

def SyntaxNodeKindSet.insert (s : SyntaxNodeKindSet) (k : SyntaxNodeKind) : SyntaxNodeKindSet :=
  PersistentHashMap.insert s k ()

/--
  Input string and related data. Recall that the `FileMap` is a helper structure for mapping
  `String.Pos` in the input string to line/column information.  -/
structure InputContext where
  input    : String
  fileName : String
  fileMap  : FileMap
  deriving Inhabited

/-- Input context derived from elaboration of previous commands. -/
structure ParserModuleContext where
  env : Environment
  options       : Options
  -- for name lookup
  currNamespace : Name := .anonymous
  openDecls     : List OpenDecl := []

/-- Parser context parts that can be updated without invalidating the parser cache. -/
structure CacheableParserContext where
  prec               : Nat
  -- used for bootstrapping only
  quotDepth          : Nat := 0
  suppressInsideQuot : Bool := false
  savedPos?          : Option String.Pos := none
  forbiddenTk?       : Option Token := none
  deriving BEq

/-- Parser context updateable in `adaptUncacheableContextFn`. -/
structure ParserContextCore extends InputContext, ParserModuleContext, CacheableParserContext where
  tokens : TokenTable

/-- Opaque parser context updateable using `adaptCacheableContextFn` and `adaptUncacheableContextFn`. -/
structure ParserContext extends ParserContextCore where private mk ::

structure Error where
  /--
    If not `missing`, used for lazily calculating `unexpected` message and range in `mkErrorMessage`.
    Otherwise, `ParserState.pos` is used as an empty range. -/
  unexpectedTk : Syntax := .missing
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

instance : ToString Error where
  toString := Error.toString

def merge (e₁ e₂ : Error) : Error :=
  match e₂ with
  -- We expect errors to be merged to be about the same token, so unconditionally copy second `unexpectedTk`
  | { unexpectedTk, unexpected := u, .. } =>
    { unexpectedTk, unexpected := if u == "" then e₁.unexpected else u, expected := e₁.expected ++ e₂.expected }

end Error

structure TokenCacheEntry where
  startPos : String.Pos := 0
  stopPos  : String.Pos := 0
  token    : Syntax := Syntax.missing

structure ParserCacheKey extends CacheableParserContext where
  parserName : Name
  pos        : String.Pos
  deriving BEq

instance : Hashable ParserCacheKey where
  -- sufficient to avoid most collisions, relatively cheap to compute
  hash k := hash (k.pos, k.parserName)

structure ParserCacheEntry where
  stx      : Syntax
  lhsPrec  : Nat
  newPos   : String.Pos
  errorMsg : Option Error

structure ParserCache where
  tokenCache  : TokenCacheEntry
  parserCache : Std.HashMap ParserCacheKey ParserCacheEntry

def initCacheForInput (input : String) : ParserCache where
  tokenCache  := { startPos := input.endPos + ' ' /- make sure it is not a valid position -/ }
  parserCache := {}

/-- A syntax array with an inaccessible prefix, used for sound caching. -/
structure SyntaxStack where
  private raw  : Array Syntax
  private drop : Nat

namespace SyntaxStack

def toSubarray (stack : SyntaxStack) : Subarray Syntax :=
  stack.raw.toSubarray stack.drop

def empty : SyntaxStack where
  raw  := #[]
  drop := 0

def size (stack : SyntaxStack) : Nat :=
  stack.raw.size - stack.drop

def isEmpty (stack : SyntaxStack) : Bool :=
  stack.size == 0

def shrink (stack : SyntaxStack) (n : Nat) : SyntaxStack :=
  { stack with raw := stack.raw.shrink (stack.drop + n) }

def push (stack : SyntaxStack) (a : Syntax) : SyntaxStack :=
  { stack with raw := stack.raw.push a }

def pop (stack : SyntaxStack) : SyntaxStack :=
  if stack.size > 0 then
    { stack with raw := stack.raw.pop }
  else stack

def back (stack : SyntaxStack) : Syntax :=
  if stack.size > 0 then
    stack.raw.back!
  else
    panic! "SyntaxStack.back: element is inaccessible"

def get! (stack : SyntaxStack) (i : Nat) : Syntax :=
  if i < stack.size then
    stack.raw.get! (stack.drop + i)
  else
    panic! "SyntaxStack.get!: element is inaccessible"

def extract (stack : SyntaxStack) (start stop : Nat) : Array Syntax :=
  stack.raw.extract (stack.drop + start) (stack.drop + stop)

instance : HAppend SyntaxStack (Array Syntax) SyntaxStack where
  hAppend stack stxs := { stack with raw := stack.raw ++ stxs }

end SyntaxStack

structure ParserState where
  stxStack : SyntaxStack := .empty
  /--
    Set to the precedence of the preceding (not surrounding) parser by `runLongestMatchParser`
    for the use of `checkLhsPrec` in trailing parsers.
    Note that with chaining, the preceding parser can be another trailing parser:
    in `1 * 2 + 3`, the preceding parser is '*' when '+' is executed. -/
  lhsPrec  : Nat := 0
  pos      : String.Pos := 0
  cache    : ParserCache
  errorMsg : Option Error := none
  recoveredErrors : Array (String.Pos × SyntaxStack × Error) := #[]

namespace ParserState

@[inline]
def hasError (s : ParserState) : Bool :=
  s.errorMsg != none

def stackSize (s : ParserState) : Nat :=
  s.stxStack.size

def restore (s : ParserState) (iniStackSz : Nat) (iniPos : String.Pos) : ParserState :=
  { s with stxStack := s.stxStack.shrink iniStackSz, errorMsg := none, pos := iniPos }

def setPos (s : ParserState) (pos : String.Pos) : ParserState :=
  { s with pos := pos }

def setCache (s : ParserState) (cache : ParserCache) : ParserState :=
  { s with cache := cache }

def pushSyntax (s : ParserState) (n : Syntax) : ParserState :=
  { s with stxStack := s.stxStack.push n }

def popSyntax (s : ParserState) : ParserState :=
  { s with stxStack := s.stxStack.pop }

def shrinkStack (s : ParserState) (iniStackSz : Nat) : ParserState :=
  { s with stxStack := s.stxStack.shrink iniStackSz }

def next (s : ParserState) (input : String) (pos : String.Pos) : ParserState :=
  { s with pos := input.next pos }

def next' (s : ParserState) (input : String) (pos : String.Pos) (h : ¬ input.atEnd pos) : ParserState :=
  { s with pos := input.next' pos h }

def mkNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err, recovered⟩ =>
    if err != none && stack.size == iniStackSz then
      -- If there is an error but there are no new nodes on the stack, use `missing` instead.
      -- Thus we ensure the property that an syntax tree contains (at least) one `missing` node
      -- if (and only if) there was a parse error.
      -- We should not create an actual node of kind `k` in this case because it would mean we
      -- choose an "arbitrary" node (in practice the last one) in an alternative of the form
      -- `node k1 p1 <|> ... <|> node kn pn` when all parsers fail. With the code below we
      -- instead return a less misleading single `missing` node without randomly selecting any `ki`.
      let stack   := stack.push Syntax.missing
      ⟨stack, lhsPrec, pos, cache, err, recovered⟩
    else
      let newNode := Syntax.node SourceInfo.none k (stack.extract iniStackSz stack.size)
      let stack   := stack.shrink iniStackSz
      let stack   := stack.push newNode
      ⟨stack, lhsPrec, pos, cache, err, recovered⟩

def mkTrailingNode (s : ParserState) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, err, errs⟩ =>
    let newNode := Syntax.node SourceInfo.none k (stack.extract (iniStackSz - 1) stack.size)
    let stack   := stack.shrink (iniStackSz - 1)
    let stack   := stack.push newNode
    ⟨stack, lhsPrec, pos, cache, err, errs⟩

def allErrors (s : ParserState) : Array (String.Pos × SyntaxStack × Error) :=
  s.recoveredErrors ++ (s.errorMsg.map (fun e => #[(s.pos, s.stxStack, e)])).getD #[]

@[inline]
def setError (s : ParserState) (e : Error) : ParserState :=
  match s with
  | ⟨stack, lhsPrec, pos, cache, _, errs⟩ => ⟨stack, lhsPrec, pos, cache, some e, errs⟩

def mkError (s : ParserState) (msg : String) : ParserState :=
  s.setError { expected := [msg] } |>.pushSyntax .missing

def mkUnexpectedError (s : ParserState) (msg : String) (expected : List String := []) (pushMissing := true) : ParserState :=
  let s := s.setError { unexpected := msg, expected }
  if pushMissing then s.pushSyntax .missing else s

def mkEOIError (s : ParserState) (expected : List String := []) : ParserState :=
  s.mkUnexpectedError "unexpected end of input" expected

def mkErrorsAt (s : ParserState) (ex : List String) (pos : String.Pos) (initStackSz? : Option Nat := none) : ParserState := Id.run do
  let mut s := s.setPos pos
  if let some sz := initStackSz? then
    s := s.shrinkStack sz
  s := s.setError { expected := ex }
  s.pushSyntax .missing

def mkErrorAt (s : ParserState) (msg : String) (pos : String.Pos) (initStackSz? : Option Nat := none) : ParserState :=
  s.mkErrorsAt [msg] pos initStackSz?

/--
  Reports given 'expected' messages at range of top stack element (assumed to be a single token).
  Replaces the element with `missing` and resets position to the token position.
  `iniPos` can be specified to avoid this position lookup but still must be identical to the token position. -/
-- We use `0` as a cheap default to save an allocation; we're unlikely to do enough backtracking at that
-- position to be significant.
def mkUnexpectedTokenErrors (s : ParserState) (ex : List String) (iniPos : String.Pos := 0) : ParserState :=
  let tk := s.stxStack.back
  let s := s.setPos (if iniPos > 0 then iniPos else tk.getPos?.get!)
  let s := s.setError { unexpectedTk := tk, expected := ex }
  s.popSyntax.pushSyntax .missing

/--
  Reports given 'expected' message at range of top stack element (assumed to be a single token).
  Replaces the element with `missing` and resets position to the token position.
  `iniPos` can be specified to avoid this position lookup but still must be identical to the token position. -/
def mkUnexpectedTokenError (s : ParserState) (msg : String) (iniPos : String.Pos := 0) : ParserState :=
  s.mkUnexpectedTokenErrors [msg] iniPos

def mkUnexpectedErrorAt (s : ParserState) (msg : String) (pos : String.Pos) : ParserState :=
  s.setPos pos |>.mkUnexpectedError msg

def toErrorMsg (ctx : InputContext) (s : ParserState) : String := Id.run do
  let mut errStr := ""
  for (pos, _stk, err) in s.allErrors do
    if errStr != "" then errStr := errStr ++ "\n"
    let pos := ctx.fileMap.toPosition pos
    errStr := errStr ++ mkErrorStringWithPos ctx.fileName pos (toString err)
  errStr

end ParserState

def ParserFn := ParserContext → ParserState → ParserState

instance : Inhabited ParserFn where
  default := fun _ s => s

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

instance : ToString FirstTokens where
  toString := toStr

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

/-- Create a simple parser combinator that inherits the `info` of the nested parser. -/
@[inline]
def withFn (f : ParserFn → ParserFn) (p : Parser) : Parser := { p with fn := f p.fn }

def adaptCacheableContextFn (f : CacheableParserContext → CacheableParserContext) (p : ParserFn) : ParserFn := fun c s =>
  p { c with toCacheableParserContext := f c.toCacheableParserContext } s

def adaptCacheableContext (f : CacheableParserContext → CacheableParserContext) : Parser → Parser :=
  withFn (adaptCacheableContextFn f)

private def withStackDrop (drop : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let initDrop := s.stxStack.drop
  let s := p c { s with stxStack.drop := drop }
  { s with stxStack.drop := initDrop }

/--
Run `p` with a fresh cache, restore outer cache afterwards.
`p` may access the entire syntax stack.
-/
def withResetCacheFn (p : ParserFn) : ParserFn := withStackDrop 0 fun c s =>
  let parserCache := s.cache.parserCache
  let s' := p c { s with cache.parserCache := {} }
  { s' with cache.parserCache := parserCache }

@[inherit_doc withResetCacheFn]
def withResetCache : Parser → Parser := withFn withResetCacheFn

/-- Run `p` under the given context transformation with a fresh cache (see also `withResetCacheFn`). -/
def adaptUncacheableContextFn (f : ParserContextCore → ParserContextCore) (p : ParserFn) : ParserFn :=
  withResetCacheFn (fun c s => p ⟨f c.toParserContextCore⟩ s)

/--
Run `p` and record result in parser cache for any further invocation with this `parserName`, parser context, and parser state.
`p` cannot access syntax stack elements pushed before the invocation in order to make caching independent of parser history.
As this excludes trailing parsers from being cached, we also reset `lhsPrec`, which is not read but set by leading parsers, to 0
in order to increase cache hits. Finally, `errorMsg` is also reset to `none` as a leading parser should not be called in the first
place if there was an error.
-/
def withCacheFn (parserName : Name) (p : ParserFn) : ParserFn := fun c s => Id.run do
  let key := ⟨c.toCacheableParserContext, parserName, s.pos⟩
  if let some r := s.cache.parserCache[key]? then
    -- TODO: turn this into a proper trace once we have these in the parser
    --dbg_trace "parser cache hit: {parserName}:{s.pos} -> {r.stx}"
    return ⟨s.stxStack.push r.stx, r.lhsPrec, r.newPos, s.cache, r.errorMsg, s.recoveredErrors⟩
  let initStackSz := s.stxStack.raw.size
  let s := withStackDrop initStackSz p c { s with lhsPrec := 0, errorMsg := none }
  if s.stxStack.raw.size != initStackSz + 1 then
    panic! s!"withCacheFn: unexpected stack growth {s.stxStack.raw}"
  { s with cache.parserCache := s.cache.parserCache.insert key ⟨s.stxStack.back, s.lhsPrec, s.pos, s.errorMsg⟩ }

@[inherit_doc withCacheFn, builtin_doc]
def withCache (parserName : Name) : Parser → Parser := withFn (withCacheFn parserName)

def ParserFn.run (p : ParserFn) (ictx : InputContext) (pmctx : ParserModuleContext) (tokens : TokenTable) (s : ParserState) : ParserState :=
  p { pmctx with
    prec           := 0
    toInputContext := ictx
    tokens
  } s
