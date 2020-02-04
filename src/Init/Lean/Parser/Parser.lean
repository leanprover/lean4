/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Data.Trie
import Init.Lean.Data.Position
import Init.Lean.Syntax
import Init.Lean.ToExpr
import Init.Lean.Environment
import Init.Lean.Attributes
import Init.Lean.Message
import Init.Lean.Compiler.InitAttr

namespace Lean
namespace Parser

def isLitKind (k : SyntaxNodeKind) : Bool :=
k == strLitKind || k == numLitKind || k == charLitKind || k == nameLitKind

abbrev mkAtom (info : SourceInfo) (val : String) : Syntax :=
Syntax.atom info val

abbrev mkIdent (info : SourceInfo) (rawVal : Substring) (val : Name) : Syntax :=
Syntax.ident (some info) rawVal val []

/- Return character after position `pos` -/
def getNext (input : String) (pos : Nat) : Char :=
input.get (input.next pos)

/- Function application precedence.
   In the standard lean language, only two tokens have precedence higher that `appPrec`.
   - The token `.` has precedence `appPrec+1`. Thus, field accesses like `g (h x).f` are parsed as `g ((h x).f)`,
     not `(g (h x)).f`
   - The token `[` when not preceded with whitespace has precedence `appPrec+1`. If there is whitespace before
     `[`, then its precedence is `appPrec`. Thus, `f a[i]` is parsed as `f (a[i])` where `a[i]` is an "find-like operation"
      (e.g., array access, map access, etc.). `f a [i]` is parsed as `(f a) [i]` where `[i]` is a singleton collection
      (e.g., a list). -/
def appPrec : Nat := 1024

structure TokenConfig :=
(val     : String)
(lbp     : Option Nat := none)
(lbpNoWs : Option Nat := none) -- optional left-binding power when there is not whitespace before the token.

namespace TokenConfig

def beq : TokenConfig → TokenConfig → Bool
| ⟨val₁, lbp₁, lbpnws₁⟩, ⟨val₂, lbp₂, lbpnws₂⟩ => val₁ == val₂ && lbp₁ == lbp₂ && lbpnws₁ == lbpnws₂

instance : HasBeq TokenConfig :=
⟨beq⟩

def toStr : TokenConfig → String
| ⟨val, some lbp, some lbpnws⟩ => val ++ ":" ++ toString lbp ++ ":" ++ toString lbpnws
| ⟨val, some lbp, none⟩        => val ++ ":" ++ toString lbp
| ⟨val, none, some lbpnws⟩     => val ++ ":none:" ++ toString lbpnws
| ⟨val, none, none⟩            => val

instance : HasToString TokenConfig := ⟨toStr⟩

end TokenConfig

structure TokenCacheEntry :=
(startPos stopPos : String.Pos := 0)
(token : Syntax := Syntax.missing)

structure ParserCache :=
(tokenCache : TokenCacheEntry := {})

def initCacheForInput (input : String) : ParserCache :=
{ tokenCache := { startPos := input.bsize + 1 /- make sure it is not a valid position -/} }

abbrev TokenTable := Trie TokenConfig

abbrev SyntaxNodeKindSet := PersistentHashMap SyntaxNodeKind Unit

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
(rbp      : Nat)
(env      : Environment)
(tokens   : TokenTable)

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
let expected   := if e.expected == [] then [] else ["expected " ++ expectedToString e.expected];
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
(cache    : ParserCache := {})
(errorMsg : Option Error := none)

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
| tokens    : List TokenConfig → FirstTokens
| optTokens : List TokenConfig → FirstTokens

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
(collectTokens : List TokenConfig → List TokenConfig   := id)
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

@[inline] def checkStackTopFn (p : Syntax → Bool) : ParserFn :=
fun c s =>
  if p s.stxStack.back then s
  else s.mkUnexpectedError "invalid leading token"

@[inline] def checkStackTop (p : Syntax → Bool) : Parser :=
{ info := epsilonInfo,
  fn   := checkStackTopFn p }

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

instance hashAndthen : HasAndthen Parser :=
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

@[inline] def leadingNode (n : SyntaxNodeKind) (p : Parser) : Parser :=
node n p

@[inline] def trailingNode (n : SyntaxNodeKind) (p : Parser) : TrailingParser :=
{ info := nodeInfo n p.info,
  fn   := trailingNodeFn n p.fn }

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

@[inline] def many1Fn (p : ParserFn) (unboxSingleton : Bool) : ParserFn :=
fun c s =>
  let iniSz  := s.stackSize;
  let s := andthenFn p (manyAux p) c s;
  if s.stackSize - iniSz == 1 && unboxSingleton then
    s
  else
    s.mkNode nullKind iniSz

@[inline] def many1 (p : Parser) (unboxSingleton := false) : Parser :=
{ info := p.info,
  fn   := many1Fn p.fn unboxSingleton }

@[specialize] private partial def sepByFnAux (p : ParserFn) (sep : ParserFn) (allowTrailingSep : Bool)
    (iniSz : Nat) (unboxSingleton : Bool)  : Bool → ParserFn
| pOpt, c, s =>
  let sz  := s.stackSize;
  let pos := s.pos;
  let s   := p c s;
  if s.hasError then
    if pOpt then
      let s := s.restore sz pos;
      if s.stackSize - iniSz == 2 && unboxSingleton then
        s.popSyntax
      else
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
      if s.stackSize - iniSz == 1 && unboxSingleton then
        s
      else
        s.mkNode nullKind iniSz
    else
      sepByFnAux allowTrailingSep c s

@[specialize] def sepByFn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz false true c s

@[specialize] def sepBy1Fn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) (unboxSingleton : Bool) : ParserFn
| c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz unboxSingleton false c s

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

@[inline] def sepBy1 (p sep : Parser) (allowTrailingSep : Bool := false) (unboxSingleton := false) : Parser :=
{ info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn unboxSingleton }

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
    let trailing := { Substring . str := input, startPos := stopPos, stopPos := stopPos' };
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
    if curr == '\\' || curr == '\"' || curr == '\'' || curr == 'n' || curr == 't' then
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
let trailing  := { Substring . str := input, startPos := stopPos, stopPos := wsStopPos };
let info      := { SourceInfo . leading := leading, pos := startPos, trailing := trailing };
s.pushSyntax (mkStxLit n val (some info))

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

private def isToken (idStartPos idStopPos : Nat) (tk : Option TokenConfig) : Bool :=
match tk with
| none    => false
| some tk =>
   -- if a token is both a symbol and a valid identifier (i.e. a keyword),
   -- we want it to be recognized as a symbol
  tk.val.bsize ≥ idStopPos - idStartPos

def mkTokenAndFixPos (startPos : Nat) (tk : Option TokenConfig) : ParserFn :=
fun c s =>
match tk with
| none    => s.mkErrorAt "token" startPos
| some tk =>
  let input     := c.input;
  let leading   := mkEmptySubstringAt input startPos;
  let val       := tk.val;
  let stopPos   := startPos + val.bsize;
  let s         := s.setPos stopPos;
  let s         := whitespace c s;
  let wsStopPos := s.pos;
  let trailing  := { Substring . str := input, startPos := stopPos, stopPos := wsStopPos };
  let atom      := mkAtom { leading := leading, pos := startPos, trailing := trailing } val;
  s.pushSyntax atom

def mkIdResult (startPos : Nat) (tk : Option TokenConfig) (val : Name) : ParserFn :=
fun c s =>
let stopPos           := s.pos;
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
  let atom            := mkIdent info rawVal val;
  s.pushSyntax atom

partial def identFnAux (startPos : Nat) (tk : Option TokenConfig) : Name → ParserFn
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

def peekToken (c : ParserContext) (s : ParserState) : ParserState × Option Syntax :=
let iniSz  := s.stackSize;
let iniPos := s.pos;
let s      := tokenFn c s;
if s.hasError then (s.restore iniSz iniPos, none)
else
  let stx := s.stxStack.back;
  (s.restore iniSz iniPos, some stx)

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

def symbolInfo (sym : String) (lbp : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbp := lbp } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbp := lbp } ] }

@[inline] def symbolFn (sym : String) : ParserFn :=
symbolFnAux sym ("'" ++ sym ++ "'")

@[inline] def symbolAux (sym : String) (lbp : Option Nat := none) : Parser :=
let sym := sym.trim;
{ info := symbolInfo sym lbp,
  fn   := symbolFn sym }

@[inline] def symbol (sym : String) (lbp : Nat) : Parser :=
symbolAux sym lbp

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
    FirstTokens.tokens [ { val := sym }, { val := "ident" } ]
  else
    FirstTokens.tokens [ { val := sym } ] }

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
| some info => info.trailing.stopPos > info.trailing.startPos
| none      => false

def checkWsBeforeFn (errorMsg : String) : ParserFn :=
fun c s =>
  let prev := s.stxStack.back;
  if checkTailWs prev then s else s.mkError errorMsg

def checkWsBefore (errorMsg : String) : Parser :=
{ info := epsilonInfo,
  fn   := checkWsBeforeFn errorMsg }

def checkTailNoWs (prev : Syntax) : Bool :=
match prev.getTailInfo with
| some info => info.trailing.stopPos == info.trailing.startPos
| none      => false

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

def symbolNoWsInfo (sym : String) (lbpNoWs : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbpNoWs := lbpNoWs } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbpNoWs := lbpNoWs } ] }

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
symbolNoWsFnAux sym ("'" ++ sym ++ "' without whitespaces around it")

/- Similar to `symbol`, but succeeds only if there is no space whitespace after leading term and after `sym`. -/
@[inline] def symbolNoWsAux (sym : String) (lbp : Option Nat) : Parser :=
let sym := sym.trim;
{ info := symbolNoWsInfo sym lbp,
  fn   := symbolNoWsFn sym }

@[inline] def symbolNoWs (sym : String) (lbp : Nat) : Parser :=
symbolNoWsAux sym lbp

def unicodeSymbolFnAux (sym asciiSym : String) (expected : List String) : ParserFn :=
satisfySymbolFn (fun s => s == sym || s == asciiSym) expected

def unicodeSymbolInfo (sym asciiSym : String) (lbp : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbp := lbp } :: { val := asciiSym, lbp := lbp } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbp := lbp }, { val := asciiSym, lbp := lbp } ] }

@[inline] def unicodeSymbolFn (sym asciiSym : String) : ParserFn :=
unicodeSymbolFnAux sym asciiSym ["'" ++ sym ++ "', '" ++ asciiSym ++ "'"]

@[inline] def unicodeSymbol (sym asciiSym : String) (lbp : Option Nat := none) : Parser :=
let sym := sym.trim;
let asciiSym := asciiSym.trim;
{ info := unicodeSymbolInfo sym asciiSym lbp,
  fn   := unicodeSymbolFn sym asciiSym }

/- Succeeds if RBP > lower -/
def checkRBPGreaterFn (lower : Nat) (errorMsg : String) : ParserFn :=
fun c s =>
  if c.rbp > lower then s.mkUnexpectedError errorMsg
  else s

def checkRBPGreater (lower : Nat) (errorMsg : String) : Parser :=
{ info := epsilonInfo,
  fn   := checkRBPGreaterFn lower errorMsg }

def mkAtomicInfo (k : String) : ParserInfo :=
{ firstTokens := FirstTokens.tokens [ { val := k } ] }

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
nodeFn `quotedSymbol (andthenFn (andthenFn (chFn '`') (rawFn (takeUntilFn (fun c => c == '`')))) (chFn '`' true))

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

instance stringToParserCoe : HasCoe String Parser :=
⟨symbolAux⟩

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

def mkLongestNodeAlt (s : ParserState) (startSize : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, _⟩ =>
  if stack.size == startSize then ⟨stack.push Syntax.missing, pos, cache, none⟩ -- parser did not create any node, then we just add `Syntax.missing`
  else if stack.size == startSize + 1 then s
  else
    -- parser created more than one node, combine them into a single node
    let node := Syntax.node nullKind (stack.extract startSize stack.size);
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

def longestMatchStep (startSize : Nat) (startPos : String.Pos) (p : ParserFn) : ParserFn :=
fun c s =>
let prevErrorMsg  := s.errorMsg;
let prevStopPos   := s.pos;
let prevSize      := s.stackSize;
let s             := s.restore prevSize startPos;
let s             := p c s;
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
  let s           := s.mkLongestNodeAlt prevSize; -- create successful alternative on the top of the stack
  let successNode := s.stxStack.back;
  let s           := s.shrinkStack startSize; -- restore stack to initial size to make sure (failure) nodes are removed from the stack
  s.pushSyntax successNode -- put successNode back on the stack

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
if !s.hasError && s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux (startSize : Nat) (startPos : String.Pos) : List Parser → ParserFn
| []    => fun _ s => longestMatchMkResult startSize s
| p::ps => fun c s =>
   let s := longestMatchStep startSize startPos p.fn c s;
   longestMatchFnAux ps c s

def longestMatchFn₁ (p : ParserFn) : ParserFn :=
fun c s =>
let startSize := s.stackSize;
let s := p c s;
if s.hasError then s else s.mkLongestNodeAlt startSize

def longestMatchFn : List Parser → ParserFn
| []    => fun _ s => s.mkError "longestMatch: empty list"
| [p]   => longestMatchFn₁ p.fn
| p::ps => fun c s =>
  let startSize := s.stackSize;
  let startPos  := s.pos;
  let s         := p.fn c s;
  if s.hasError then
    let s := s.shrinkStack startSize;
    longestMatchFnAux startSize startPos ps c s
  else
    let s := s.mkLongestNodeAlt startSize;
    longestMatchFnAux startSize startPos ps c s

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

structure PrattParsingTables :=
(leadingTable    : TokenMap Parser := {})
(leadingParsers  : List Parser := []) -- for supporting parsers we cannot obtain first token
(trailingTable   : TokenMap TrailingParser := {})
(trailingParsers : List TrailingParser := []) -- for supporting parsers such as function application

instance PrattParsingTables.inhabited : Inhabited PrattParsingTables := ⟨{}⟩

/--
  Each parser category is implemented using Pratt's parser.
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
  function). -/
structure ParserCategory :=
(tables : PrattParsingTables) (leadingIdentAsSymbol : Bool)

instance ParserCategory.inhabited : Inhabited ParserCategory := ⟨{ tables := {}, leadingIdentAsSymbol := false }⟩

abbrev ParserCategories := PersistentHashMap Name ParserCategory

def currLbp (left : Syntax) (c : ParserContext) (s : ParserState) : ParserState × Nat :=
let (s, stx?) := peekToken c s;
match stx? with
| some stx@(Syntax.atom _ sym) =>
  if sym == "$" && checkTailNoWs stx then (s, appPrec) -- TODO: split `lbpNoWs` into "before" and "after", and set right lbp for '$' in antiquotations
  else match c.tokens.matchPrefix sym 0 with
  | (_, some tk) => match tk.lbp, tk.lbpNoWs with
    | some lbp, none         => (s, lbp)
    | none, some lbpNoWs     => (s, lbpNoWs)
    | some lbp, some lbpNoWs => if checkTailNoWs left then (s, lbpNoWs) else (s, lbp)
    | none, none             => (s, 0)
  | _            => (s, 0)
| some (Syntax.ident _ _ _ _) => (s, appPrec)
-- TODO(Leo): add support for associating lbp with syntax node kinds.
| some (Syntax.node k _)      =>
  if isLitKind k || k == fieldIdxKind then
    (s, appPrec)
  else
    (s, 0)
| _                           => (s, 0)

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) (leadingIdentAsSymbol : Bool) : ParserState × List α :=
let (s, stx) := peekToken c s;
let find (n : Name) : ParserState × List α :=
  match map.find n with
  | some as => (s, as)
  | _       => (s, []);
match stx with
| some (Syntax.atom _ sym)      => find (mkNameSimple sym)
| some (Syntax.ident _ _ val _) =>
  if leadingIdentAsSymbol then
    match map.find val with
    | some as => match map.find identKind with
      | some as' => (s, as ++ as')
      | _        => (s, as)
    | none    => find identKind
  else
    find identKind
| some (Syntax.node k _)        => find k
| _                             => (s, [])

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
if s.stackSize == iniSz + 1 then s
else s.mkNode nullKind iniSz -- throw error instead?

def leadingParser (kind : Name) (tables : PrattParsingTables) (preLeadingParser : Parser) (leadingIdentAsSymbol : Bool) : ParserFn :=
orelseFn preLeadingParser.fn $ fun c s =>
  let iniSz   := s.stackSize;
  let (s, ps) := indexed tables.leadingTable c s leadingIdentAsSymbol;
  let ps      := tables.leadingParsers ++ ps;
  if ps.isEmpty then
    s.mkError (toString kind)
  else
    let s := longestMatchFn ps c s;
    mkResult s iniSz

def trailingLoopStep (tables : PrattParsingTables) (ps : List Parser) : ParserFn :=
fun c s =>
  orelseFn (longestMatchFn ps) (anyOfFn tables.trailingParsers) c s

private def mkTrailingResult (s : ParserState) (iniSz : Nat) : ParserState :=
let s := mkResult s iniSz;
-- Stack contains `[..., left, result]`
-- We must remove `left`
let result := s.stxStack.back;
let s      := s.popSyntax.popSyntax;
s.pushSyntax result

partial def trailingLoop (tables : PrattParsingTables) (c : ParserContext) : ParserState → ParserState
| s =>
  let left := s.stxStack.back;
  let (s, lbp) := currLbp left c s;
  if c.rbp ≥ lbp then s
  else
    let iniSz         := s.stackSize;
    let identAsSymbol := false;
    let (s, ps)       := indexed tables.trailingTable c s identAsSymbol;
    if ps.isEmpty && tables.trailingParsers.isEmpty then
      s -- no available trailing parser
    else
      let s := trailingLoopStep tables ps c s;
      if s.hasError then s
      else
        let s := mkTrailingResult s iniSz;
        trailingLoop s

/--
  Implements a recursive precedence parser according to Pratt's algorithm.

  `preLeadingParser` is a parser that is preferred over all other leading
  parsers. We use it to inject the antiquotation parser into syntax categories.
  It should not be added to the regular leading parsers because it would heavily
  overlap with antiquotation parsers nested inside them. -/
def prattParser (kind : Name) (tables : PrattParsingTables) (preLeadingParser : Parser) (leadingIdentAsSymbol : Bool) : ParserFn :=
fun c s =>
  let left := s.stxStack.back;
  let (s, lbp) := currLbp left c s;
  if c.rbp > lbp then s.mkUnexpectedError "unexpected token"
  else
    let s := leadingParser kind tables preLeadingParser leadingIdentAsSymbol c s;
    if s.hasError then s
    else
      trailingLoop tables c s

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

def categoryParser (catName : Name) (rbp : Nat) : Parser :=
{ fn := fun c s => categoryParserFn catName { rbp := rbp, .. c } s }

-- Define `termParser` here because we need it for antiquotations
@[inline] def termParser (rbp : Nat := 0) : Parser :=
categoryParser `term rbp

/- ============== -/
/- Antiquotations -/
/- ============== -/

def dollarSymbol : Parser := symbol "$" 1

/-- Fail if previous token is immediately followed by ':'. -/
private def noImmediateColon : Parser :=
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
  | s'@{ errorMsg := some msg } => { s' with errorMsg := some { msg with expected := [] } }
  | s'                          => s'

def setExpected (expected : List String) (p : Parser) : Parser :=
{ fn := setExpectedFn expected p.fn, info := p.info }

def pushNone : Parser :=
{ fn := fun c s => s.pushSyntax mkNullNode }

/-
  We support two kinds of antiquotations: `$id` and `$(t)`, where `id` is a term identifier and `t` is a term.

  TODO: we are making both cases look like syntax terms. Reason: the current expander expects a term.
  We should remove this hack and modify the expander. This hack is bad since it relies on how we define `id` and `paren` in
  the term parser at `Term.lean`. -/
private def antiquotId : Parser         := node `Lean.Parser.Term.id (identNoAntiquot >> pushNone)
private def antiquotNestedExpr : Parser := node `Lean.Parser.Term.paren ("(" >> node nullKind (termParser >> pushNone) >> ")")
private def antiquotExpr : Parser       := antiquotId <|> antiquotNestedExpr

/--
  Define parser for `$e` (if anonymous == true) and `$e:name`. Both
  forms can also be used with an appended `*` to turn them into an
  antiquotation "splice". If `kind` is given, it will additionally be checked
  when evaluating `match_syntax`. -/
def mkAntiquot (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parser :=
let kind := (kind.getD Name.anonymous) ++ `antiquot;
let nameP := checkNoWsBefore ("no space before ':" ++ name ++ "'") >> symbolAux ":" >> nonReservedSymbol name;
-- if parsing the kind fails and `anonymous` is true, check that we're not ignoring a different
-- antiquotation kind via `noImmediateColon`
let nameP := if anonymous then nameP <|> noImmediateColon >> pushNone >> pushNone else nameP;
-- antiquotations are not part of the "standard" syntax, so hide "expected '$'" on error
node kind $ try $ setExpected [] dollarSymbol >> checkNoWsBefore "no space before" >> antiquotExpr >> nameP >> optional (checkNoWsBefore "" >> "*")

/- ===================== -/
/- End of Antiquotations -/
/- ===================== -/

def nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : Parser) : Parser :=
mkAntiquot name kind false <|> node kind p

def ident : Parser :=
mkAntiquot "ident" identKind <|> identNoAntiquot

-- `ident` and `rawIdent` produce the same syntax tree, so we reuse the antiquotation kind name
def rawIdent : Parser :=
mkAntiquot "ident" identKind <|> rawIdentNoAntiquot

def numLit : Parser :=
mkAntiquot "numLit" numLitKind <|> numLitNoAntiquot

def strLit : Parser :=
mkAntiquot "strLit" strLitKind <|> strLitNoAntiquot

def charLit : Parser :=
mkAntiquot "charLit" charLitKind <|> charLitNoAntiquot

def nameLit : Parser :=
mkAntiquot "nameLit" nameLitKind <|> nameLitNoAntiquot

def categoryParserOfStackFn (offset : Nat) : ParserFn :=
fun ctx s =>
  let stack := s.stxStack;
  if stack.size < offset + 1 then
    s.mkUnexpectedError ("failed to determine parser category using syntax stack, stack is too small")
  else
    match stack.get! (stack.size - offset - 1) with
    | Syntax.ident _ _ catName _ => categoryParserFn catName ctx s
    | _ => s.mkUnexpectedError ("failed to determine parser category using syntax stack, the specified element on the stack is not an identifier")

def categoryParserOfStack (offset : Nat) (rbp : Nat := 0) : Parser :=
{ fn := fun c s => categoryParserOfStackFn offset { rbp := rbp, .. c } s }

def mkBuiltinTokenTable : IO (IO.Ref TokenTable) := IO.mkRef {}
@[init mkBuiltinTokenTable] constant builtinTokenTable : IO.Ref TokenTable := arbitrary _

/- Global table with all SyntaxNodeKind's -/
def mkBuiltinSyntaxNodeKindSetRef : IO (IO.Ref SyntaxNodeKindSet) := IO.mkRef {}
@[init mkBuiltinSyntaxNodeKindSetRef] constant builtinSyntaxNodeKindSetRef : IO.Ref SyntaxNodeKindSet := arbitrary _

def mkBuiltinParserCategories : IO (IO.Ref ParserCategories) := IO.mkRef {}
@[init mkBuiltinParserCategories] constant builtinParserCategoriesRef : IO.Ref ParserCategories := arbitrary _

private def throwParserCategoryAlreadyDefined {α} (catName : Name) : ExceptT String Id α :=
throw ("parser category '" ++ toString catName ++ "' has already been defined")

private def addParserCategoryCore (categories : ParserCategories) (catName : Name) (initial : ParserCategory) : Except String ParserCategories :=
if categories.contains catName then
  throwParserCategoryAlreadyDefined catName
else
  pure $ categories.insert catName initial

/-- All builtin parser categories are Pratt's parsers -/
private def addBuiltinParserCategory (catName : Name) (leadingIdentAsSymbol : Bool) : IO Unit := do
categories ← builtinParserCategoriesRef.get;
categories ← IO.ofExcept $ addParserCategoryCore categories catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol};
builtinParserCategoriesRef.set categories

inductive ParserExtensionOleanEntry
| token     (val : TokenConfig) : ParserExtensionOleanEntry
| kind      (val : SyntaxNodeKind) : ParserExtensionOleanEntry
| category  (catName : Name) (leadingIdentAsSymbol : Bool)
| parser    (catName : Name) (declName : Name) : ParserExtensionOleanEntry

inductive ParserExtensionEntry
| token     (val : TokenConfig) : ParserExtensionEntry
| kind      (val : SyntaxNodeKind) : ParserExtensionEntry
| category  (catName : Name) (leadingIdentAsSymbol : Bool)
| parser    (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : ParserExtensionEntry

structure ParserExtensionState :=
(tokens      : TokenTable := {})
(kinds       : SyntaxNodeKindSet := {})
(categories  : ParserCategories := {})
(newEntries  : List ParserExtensionOleanEntry := [])

instance ParserExtensionState.inhabited : Inhabited ParserExtensionState := ⟨{}⟩

abbrev ParserExtension := PersistentEnvExtension ParserExtensionOleanEntry ParserExtensionEntry ParserExtensionState

private def ParserExtension.mkInitial : IO ParserExtensionState := do
tokens     ← builtinTokenTable.get;
kinds      ← builtinSyntaxNodeKindSetRef.get;
categories ← builtinParserCategoriesRef.get;
pure { tokens := tokens, kinds := kinds, categories := categories }

private def mergePrecendences (msgPreamble : String) (sym : String) : Option Nat → Option Nat → Except String (Option Nat)
| none,   b      => pure b
| a,      none   => pure a
| some a, some b =>
  if a == b then pure $ some a
  else
    throw $ msgPreamble ++ "precedence mismatch for '" ++ toString sym ++ "', previous: " ++ toString a ++ ", new: " ++ toString b

private def addTokenConfig (tokens : TokenTable) (tk : TokenConfig) : Except String TokenTable := do
if tk.val == "" then throw "invalid empty symbol"
else match tokens.find tk.val with
  | none       => pure $ tokens.insert tk.val tk
  | some oldTk => do
    lbp     ← mergePrecendences "" tk.val oldTk.lbp tk.lbp;
    lbpNoWs ← mergePrecendences "(no whitespace) " tk.val oldTk.lbpNoWs tk.lbpNoWs;
    pure $ tokens.insert tk.val { lbp := lbp, lbpNoWs := lbpNoWs, .. tk }

def throwUnknownParserCategory {α} (catName : Name) : ExceptT String Id α :=
throw ("unknown parser category '" ++ toString catName ++ "'")

def addLeadingParser (categories : ParserCategories) (catName : Name) (parserName : Name) (p : Parser) : Except String ParserCategories :=
match categories.find? catName with
| none     =>
  throwUnknownParserCategory catName
| some cat =>
  let addTokens (tks : List TokenConfig) : Except String ParserCategories :=
    let tks    := tks.map $ fun tk => mkNameSimple tk.val;
    let tables := tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { leadingTable := tables.leadingTable.insert tk p, .. tables }) cat.tables;
    pure $ categories.insert catName { tables := tables, .. cat };
  match p.info.firstTokens with
  | FirstTokens.tokens tks    => addTokens tks
  | FirstTokens.optTokens tks => addTokens tks
  | _ =>
    let tables := { leadingParsers := p :: cat.tables.leadingParsers, .. cat.tables };
    pure $ categories.insert catName { tables := tables, .. cat }

private def addTrailingParserAux (tables : PrattParsingTables) (p : TrailingParser) : PrattParsingTables :=
let addTokens (tks : List TokenConfig) : PrattParsingTables :=
  let tks := tks.map $ fun tk => mkNameSimple tk.val;
  tks.eraseDups.foldl (fun (tables : PrattParsingTables) tk => { trailingTable := tables.trailingTable.insert tk p, .. tables }) tables;
match p.info.firstTokens with
| FirstTokens.tokens tks    => addTokens tks
| FirstTokens.optTokens tks => addTokens tks
| _                         => { trailingParsers := p :: tables.trailingParsers, .. tables }

def addTrailingParser (categories : ParserCategories) (catName : Name) (p : TrailingParser) : Except String ParserCategories :=
match categories.find? catName with
| none     => throwUnknownParserCategory catName
| some cat => pure $ categories.insert catName { tables := addTrailingParserAux cat.tables p, .. cat }

def addParser (categories : ParserCategories) (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : Except String ParserCategories :=
match leading, p with
| true, p  => addLeadingParser categories catName declName p
| false, p => addTrailingParser categories catName p

def addParserTokens (tokenTable : TokenTable) (info : ParserInfo) : Except String TokenTable :=
let newTokens := info.collectTokens [];
newTokens.foldlM addTokenConfig tokenTable

private def updateBuiltinTokens (info : ParserInfo) (declName : Name) : IO Unit := do
tokenTable ← builtinTokenTable.swap {};
match addParserTokens tokenTable info with
| Except.ok tokenTable => builtinTokenTable.set tokenTable
| Except.error msg     => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', " ++ msg))

def addBuiltinParser (catName : Name) (declName : Name) (leading : Bool) (p : Parser) : IO Unit := do
categories ← builtinParserCategoriesRef.get;
categories ← IO.ofExcept $ addParser categories catName declName leading p;
builtinParserCategoriesRef.set categories;
builtinSyntaxNodeKindSetRef.modify p.info.collectKinds;
updateBuiltinTokens p.info declName

def addBuiltinLeadingParser (catName : Name) (declName : Name) (p : Parser) : IO Unit :=
addBuiltinParser catName declName true p

def addBuiltinTrailingParser (catName : Name) (declName : Name) (p : TrailingParser) : IO Unit :=
addBuiltinParser catName declName false p

private def ParserExtension.addEntry (s : ParserExtensionState) (e : ParserExtensionEntry) : ParserExtensionState :=
match e with
| ParserExtensionEntry.token tk =>
  match addTokenConfig s.tokens tk with
  | Except.ok tokens => { tokens := tokens, newEntries := ParserExtensionOleanEntry.token tk :: s.newEntries, .. s }
  | _                => unreachable!
| ParserExtensionEntry.kind k =>
  { kinds := s.kinds.insert k, newEntries := ParserExtensionOleanEntry.kind k :: s.newEntries, .. s }
| ParserExtensionEntry.category catName leadingIdentAsSymbol =>
  if s.categories.contains catName then s
  else { categories := s.categories.insert catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol },
         newEntries := ParserExtensionOleanEntry.category catName leadingIdentAsSymbol :: s.newEntries, .. s }
| ParserExtensionEntry.parser catName declName leading parser =>
  match addParser s.categories catName declName leading parser with
  | Except.ok categories => { categories := categories, newEntries := ParserExtensionOleanEntry.parser catName declName :: s.newEntries, .. s }
  | _ => unreachable!

def compileParserDescr (categories : ParserCategories) : ParserDescr → Except String (Parser)
| ParserDescr.andthen d₁ d₂                       => andthen <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.orelse d₁ d₂                        => orelse <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.optional d                          => optional <$> compileParserDescr d
| ParserDescr.lookahead d                         => lookahead <$> compileParserDescr d
| ParserDescr.try d                               => try <$> compileParserDescr d
| ParserDescr.many d                              => many <$> compileParserDescr d
| ParserDescr.many1 d                             => many1 <$> compileParserDescr d
| ParserDescr.sepBy d₁ d₂                         => sepBy <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.sepBy1 d₁ d₂                        => sepBy1 <$> compileParserDescr d₁ <*> compileParserDescr d₂
| ParserDescr.node k d                            => node k <$> compileParserDescr d
| ParserDescr.trailingNode k d                    => trailingNode k <$> compileParserDescr d
| ParserDescr.symbol tk lbp                       => pure $ symbolAux tk lbp
| ParserDescr.numLit                              => pure $ numLit
| ParserDescr.strLit                              => pure $ strLit
| ParserDescr.charLit                             => pure $ charLit
| ParserDescr.nameLit                             => pure $ nameLit
| ParserDescr.ident                               => pure $ ident
| ParserDescr.nonReservedSymbol tk includeIdent   => pure $ nonReservedSymbol tk includeIdent
| ParserDescr.parser catName rbp =>
  match categories.find? catName with
  | some _ => pure $ categoryParser catName rbp
  | none   => throwUnknownParserCategory catName

unsafe def mkParserOfConstantUnsafe (env : Environment) (categories : ParserCategories) (constName : Name) : Except String (Bool × Parser) :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const `Lean.Parser.TrailingParser _ _ => do
    p ← env.evalConst Parser constName;
    pure ⟨false, p⟩
  | Expr.const `Lean.Parser.Parser _ _ => do
    p ← env.evalConst Parser constName;
    pure ⟨true, p⟩
  | Expr.const `Lean.ParserDescr _ _ => do
    d ← env.evalConst ParserDescr constName;
    p ← compileParserDescr categories d;
    pure ⟨true, p⟩
  | Expr.const `Lean.TrailingParserDescr _ _ => do
    d ← env.evalConst TrailingParserDescr constName;
    p ← compileParserDescr categories d;
    pure ⟨false, p⟩
  | _ => throw ("unexpected parser type at '" ++ toString constName ++ "' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected")

@[implementedBy mkParserOfConstantUnsafe]
constant mkParserOfConstant (env : Environment) (categories : ParserCategories) (constName : Name) : Except String (Bool × Parser) :=
arbitrary _

private def ParserExtension.addImported (env : Environment) (es : Array (Array ParserExtensionOleanEntry)) : IO ParserExtensionState := do
s ← ParserExtension.mkInitial;
es.foldlM
  (fun s entries =>
    entries.foldlM
      (fun s entry =>
       match entry with
       | ParserExtensionOleanEntry.token tk => do
         tokens ← IO.ofExcept (addTokenConfig s.tokens tk);
         pure { tokens := tokens, .. s }
       | ParserExtensionOleanEntry.kind k =>
         pure { kinds := s.kinds.insert k, .. s }
       | ParserExtensionOleanEntry.category catName leadingIdentAsSymbol => do
         categories ← IO.ofExcept (addParserCategoryCore s.categories catName { tables := {}, leadingIdentAsSymbol := leadingIdentAsSymbol});
         pure { categories := categories, .. s }
       | ParserExtensionOleanEntry.parser catName declName =>
         match mkParserOfConstant env s.categories declName with
        | Except.ok p     =>
          match addParser s.categories catName declName p.1 p.2 with
          | Except.ok categories => pure { categories := categories, .. s }
          | Except.error ex      => throw (IO.userError ex)
        | Except.error ex => throw (IO.userError ex))
      s)
  s

def mkParserExtension : IO ParserExtension :=
registerPersistentEnvExtension {
  name            := `parserExt,
  mkInitial       := ParserExtension.mkInitial,
  addImportedFn   := ParserExtension.addImported,
  addEntryFn      := ParserExtension.addEntry,
  exportEntriesFn := fun s => s.newEntries.reverse.toArray,
  statsFn         := fun s => format "number of local entries: " ++ format s.newEntries.length
}

@[init mkParserExtension]
constant parserExtension : ParserExtension := arbitrary _

def isParserCategory (env : Environment) (catName : Name) : Bool :=
(parserExtension.getState env).categories.contains catName

def addParserCategory (env : Environment) (catName : Name) (leadingIdentAsSymbol : Bool) : Except String Environment := do
if isParserCategory env catName then
  throwParserCategoryAlreadyDefined catName
else
  pure $ parserExtension.addEntry env $ ParserExtensionEntry.category catName leadingIdentAsSymbol

/-
  Return true if in the given category leading identifiers in parsers may be treated as atoms/symbols.
  See comment at `ParserCategory`. -/
def leadingIdentAsSymbol (env : Environment) (catName : Name) : Bool :=
match (parserExtension.getState env).categories.find? catName with
| none     => false
| some cat => cat.leadingIdentAsSymbol

private def catNameToString : Name → String
| Name.str Name.anonymous s _ => s
| n                           => n.toString

def categoryParserFnImpl (catName : Name) : ParserFn :=
fun ctx s =>
  let categories := (parserExtension.getState ctx.env).categories;
  match categories.find? catName with
  | some cat =>
    -- allow "anonymous" antiquotations `$x` for the `term` category only
    -- TODO: make customizable
    -- one good example for a category that should not be anonymous is
    -- `index` in `tests/lean/run/bigop.lean`.
    let anonAntiquot := catName == `term;
    let preP := mkAntiquot (catNameToString catName) none anonAntiquot;
    prattParser catName cat.tables preP cat.leadingIdentAsSymbol ctx s
  | none     => s.mkUnexpectedError ("unknown parser category '" ++ toString catName ++ "'")

@[init] def setCategoryParserFnRef : IO Unit :=
categoryParserFnRef.set categoryParserFnImpl

def addToken (env : Environment) (tk : TokenConfig) : Except String Environment := do
-- Recall that `ParserExtension.addEntry` is pure, and assumes `addTokenConfig` does not fail.
-- So, we must run it here to handle exception.
addTokenConfig (parserExtension.getState env).tokens tk;
pure $ parserExtension.addEntry env $ ParserExtensionEntry.token tk

def addSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Environment :=
parserExtension.addEntry env $ ParserExtensionEntry.kind k

def isValidSyntaxNodeKind (env : Environment) (k : SyntaxNodeKind) : Bool :=
let kinds := (parserExtension.getState env).kinds;
kinds.contains k || k == choiceKind || k == identKind || isLitKind k

def getSyntaxNodeKinds (env : Environment) : List SyntaxNodeKind := do
let kinds := (parserExtension.getState env).kinds;
kinds.foldl (fun ks k _ => k::ks) []

def getTokenTable (env : Environment) : TokenTable :=
(parserExtension.getState env).tokens

def mkInputContext (input : String) (fileName : String) : InputContext :=
{ input    := input,
  fileName := fileName,
  fileMap  := input.toFileMap }

def mkParserContext (env : Environment) (ctx : InputContext) : ParserContext :=
{ rbp            := 0,
  toInputContext := ctx,
  env            := env,
  tokens         := getTokenTable env }

def mkParserState (input : String) : ParserState :=
{ cache := initCacheForInput input }

/- convenience function for testing -/
def runParserCategory (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String Syntax :=
let c := mkParserContext env (mkInputContext input fileName);
let s := mkParserState input;
let s := whitespace c s;
let s := categoryParserFnImpl catName c s;
if s.hasError then
  Except.error (s.toErrorMsg c)
else
  Except.ok s.stxStack.back

def declareBuiltinParser (env : Environment) (addFnName : Name) (catName : Name) (declName : Name) : IO Environment :=
let name := `_regBuiltinParser ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkAppN (mkConst addFnName) #[toExpr catName, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

def declareLeadingBuiltinParser (env : Environment) (catName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinLeadingParser catName declName

def declareTrailingBuiltinParser (env : Environment) (catName : Name) (declName : Name) : IO Environment :=
declareBuiltinParser env `Lean.Parser.addBuiltinTrailingParser catName declName

private def BuiltinParserAttribute.add (attrName : Name) (catName : Name)
    (env : Environment) (declName : Name) (args : Syntax) (persistent : Bool) : IO Environment := do
when args.hasArgs $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', unexpected argument"));
unless persistent $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', must be persistent"));
match env.find? declName with
| none  => throw $ IO.userError "unknown declaration"
| some decl =>
  match decl.type with
 | Expr.const `Lean.Parser.TrailingParser _ _ =>
   declareTrailingBuiltinParser env catName declName
 | Expr.const `Lean.Parser.Parser _ _ =>
   declareLeadingBuiltinParser env catName declName
 | _ =>
   throw (IO.userError ("unexpected parser type at '" ++ toString declName ++ "' (`Parser` or `TrailingParser` expected"))

/-
The parsing tables for builtin parsers are "stored" in the extracted source code.
-/
def registerBuiltinParserAttribute (attrName : Name) (catName : Name) (leadingIdentAsSymbol := false) : IO Unit := do
addBuiltinParserCategory catName leadingIdentAsSymbol;
registerBuiltinAttribute {
 name            := attrName,
 descr           := "Builtin parser",
 add             := BuiltinParserAttribute.add attrName catName,
 applicationTime := AttributeApplicationTime.afterCompilation
}

private def ParserAttribute.add (attrName : Name) (catName : Name) (env : Environment) (declName : Name) (args : Syntax) (persistent : Bool) : IO Environment := do
when args.hasArgs $ throw (IO.userError ("invalid attribute '" ++ toString attrName ++ "', unexpected argument"));
let categories := (parserExtension.getState env).categories;
match mkParserOfConstant env categories declName with
| Except.error ex => throw (IO.userError ex)
| Except.ok p     => do
  let leading    := p.1;
  let parser     := p.2;
  let tokens     := parser.info.collectTokens [];
  env ← tokens.foldlM
    (fun env token =>
      match addToken env token with
      | Except.ok env    => pure env
      | Except.error msg => throw (IO.userError ("invalid parser '" ++ toString declName ++ "', " ++ msg)))
    env;
  let kinds := parser.info.collectKinds {};
  let env := kinds.foldl (fun env kind _ => addSyntaxNodeKind env kind) env;
  match addParser categories catName declName leading parser with
  | Except.ok _     => pure $ parserExtension.addEntry env $ ParserExtensionEntry.parser catName declName leading parser
  | Except.error ex => throw (IO.userError ex)

def mkParserAttributeImpl (attrName : Name) (catName : Name) : AttributeImpl :=
{ name            := attrName,
  descr           := "parser",
  add             := ParserAttribute.add attrName catName,
  applicationTime := AttributeApplicationTime.afterCompilation }

/- A builtin parser attribute that can be extended by users. -/
def registerBuiltinDynamicParserAttribute (attrName : Name) (catName : Name) : IO Unit := do
registerBuiltinAttribute (mkParserAttributeImpl attrName catName)

@[init] private def registerParserAttributeImplBuilder : IO Unit :=
registerAttributeImplBuilder `parserAttr $ fun args =>
  match args with
  | [DataValue.ofName attrName, DataValue.ofName catName] => pure $ mkParserAttributeImpl attrName catName
  | _ => throw ("invalid parser attribute implementation builder arguments")

def registerParserCategory (env : Environment) (attrName : Name) (catName : Name) (leadingIdentAsSymbol := false) : IO Environment := do
env ← IO.ofExcept $ addParserCategory env catName leadingIdentAsSymbol;
registerAttributeOfBuilder env `parserAttr [DataValue.ofName attrName, DataValue.ofName catName]

-- declare `termParser` here since it is used everywhere via antiquotations

@[init] def regBuiltinTermParserAttr : IO Unit :=
registerBuiltinParserAttribute `builtinTermParser `term

@[init] def regTermParserAttribute : IO Unit :=
registerBuiltinDynamicParserAttribute `termParser `term

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
mkAntiquot "fieldIdx" `fieldIdx <|>
{ fn   := fieldIdxFn,
  info := mkAtomicInfo "fieldIdx" }

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
