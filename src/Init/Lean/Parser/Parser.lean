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
    -- If there is an error but there are no new nodes on the stack, we just return `d`
    s
  else
    let newNode := Syntax.node k (stack.extract iniStackSz stack.size);
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

def ParserArg : ParserKind → Type
| ParserKind.leading => Nat
| ParserKind.trailing => Syntax

export ParserKind (leading trailing)

def BasicParserFn := ParserContext → ParserState → ParserState

def ParserFn (k : ParserKind) := ParserArg k → BasicParserFn

instance ParserFn.inhabited (k : ParserKind) : Inhabited (ParserFn k) := ⟨fun _ _ => id⟩

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

@[inline] def toTrailing (p : Parser) (rbp : Nat := 0) : TrailingParser :=
{ info := p.info,
  fn   := fun a => p.fn rbp }

@[inline] def checkLeadingFn (p : Syntax → Bool) : ParserFn trailing :=
fun a c s =>
  if p a then s
  else s.mkUnexpectedError "invalid leading token"

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
{ collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.seq q.firstTokens }

@[inline] def andthen {k : ParserKind} (p q : Parser k) : Parser k :=
{ info := andthenInfo p.info q.info,
  fn   := andthenFn p.fn q.fn }

instance hashAndthen {k : ParserKind} : HasAndthen (Parser k) :=
⟨andthen⟩

@[inline] def nodeFn {k : ParserKind} (n : SyntaxNodeKind) (p : ParserFn k) : ParserFn k
| a, c, s =>
  let iniSz := s.stackSize;
  let s     := p a c s;
  s.mkNode n iniSz

@[noinline] def nodeInfo (n : SyntaxNodeKind) (p : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens,
  collectKinds  := fun s => (p.collectKinds s).insert n,
  firstTokens   := p.firstTokens }

@[inline] def node {k : ParserKind} (n : SyntaxNodeKind) (p : Parser k) : Parser k :=
{ info := nodeInfo n p.info,
  /- Remark: the compiler currently does not eta-expand structure fields.
     So, we force it here to trigger inlining at `node` combinators. -/
  fn   := nodeFn n p.fn }

@[inline] def group {k : ParserKind} (p : Parser k) : Parser k :=
node nullKind p

@[inline] def leadingNode (n : SyntaxNodeKind) (p : Parser leading) : Parser :=
node n p

@[inline] def trailingNode (n : SyntaxNodeKind) (p : Parser trailing) : TrailingParser :=
node n p

def mergeOrElseErrors (s : ParserState) (error1 : Error) (iniPos : Nat) : ParserState :=
match s with
| ⟨stack, pos, cache, some error2⟩ =>
  if pos == iniPos then ⟨stack, pos, cache, some (error1.merge error2)⟩
  else s
| other => other

@[inline] def orelseFn {k : ParserKind} (p q : ParserFn k) : ParserFn k
| a, c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  match s.errorMsg with
  | some errorMsg =>
    if s.pos == iniPos then
      mergeOrElseErrors (q a c (s.restore iniSz iniPos)) errorMsg iniPos
    else
      s
  | none => s

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ q.collectTokens,
  collectKinds  := p.collectKinds ∘ q.collectKinds,
  firstTokens   := p.firstTokens.merge q.firstTokens }

@[inline] def orelse {k : ParserKind} (p q : Parser k) : Parser k :=
{ info := orelseInfo p.info q.info,
  fn   := orelseFn p.fn q.fn }

instance hashOrelse {k : ParserKind} : HasOrelse (Parser k) :=
⟨orelse⟩

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ collectTokens := info.collectTokens,
  collectKinds  := info.collectKinds }

@[inline] def tryFn {k : ParserKind} (p : ParserFn k ) : ParserFn k
| a, c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  match p a c s with
  | ⟨stack, _, cache, some msg⟩ => ⟨stack.shrink iniSz, iniPos, cache, some msg⟩
  | other                       => other

@[inline] def try {k : ParserKind} (p : Parser k) : Parser k :=
{ info := p.info,
  fn   := tryFn p.fn }

@[inline] def optionalFn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  let s      := if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else s;
  s.mkNode nullKind iniSz

@[noinline] def optionaInfo (p : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens,
  collectKinds  := p.collectKinds,
  firstTokens   := p.firstTokens.toOptional }

@[inline] def optional {k : ParserKind} (p : Parser k) : Parser k :=
{ info := optionaInfo p.info,
  fn   := optionalFn p.fn }

@[inline] def lookaheadFn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  if s.hasError then s else s.restore iniSz iniPos

@[inline] def lookahead {k : ParserKind} (p : Parser k) : Parser k :=
{ info := p.info,
  fn   := lookaheadFn p.fn }

@[specialize] partial def manyAux {k : ParserKind} (p : ParserFn k) : ParserFn k
| a, c, s =>
  let iniSz  := s.stackSize;
  let iniPos := s.pos;
  let s      := p a c s;
  if s.hasError then
    if iniPos == s.pos then s.restore iniSz iniPos else s
  else if iniPos == s.pos then s.mkUnexpectedError "invalid 'many' parser combinator application, parser did not consume anything"
  else manyAux a c s

@[inline] def manyFn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let s := manyAux p a c s;
  s.mkNode nullKind iniSz

@[inline] def many {k : ParserKind} (p : Parser k) : Parser k :=
{ info := noFirstTokenInfo p.info,
  fn   := manyFn p.fn }

@[inline] def many1Fn {k : ParserKind} (p : ParserFn k) (unboxSingleton : Bool) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let s := andthenFn p (manyAux p) a c s;
  if s.stackSize - iniSz == 1 && unboxSingleton then
    s
  else
    s.mkNode nullKind iniSz

@[inline] def many1 {k : ParserKind} (p : Parser k) (unboxSingleton := false) : Parser k :=
{ info := p.info,
  fn   := many1Fn p.fn unboxSingleton }

@[specialize] private partial def sepByFnAux {k : ParserKind} (p : ParserFn k) (sep : ParserFn k) (allowTrailingSep : Bool)
    (iniSz : Nat) (unboxSingleton : Bool)  : Bool → ParserFn k
| pOpt, a, c, s =>
  let sz  := s.stackSize;
  let pos := s.pos;
  let s   := p a c s;
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
    let s   := sep a c s;
    if s.hasError then
      let s := s.restore sz pos;
      if s.stackSize - iniSz == 1 && unboxSingleton then
        s
      else
        s.mkNode nullKind iniSz
    else
      sepByFnAux allowTrailingSep a c s

@[specialize] def sepByFn {k : ParserKind} (allowTrailingSep : Bool) (p : ParserFn k) (sep : ParserFn k) : ParserFn k
| a, c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz false true a c s

@[specialize] def sepBy1Fn {k : ParserKind} (allowTrailingSep : Bool) (p : ParserFn k) (sep : ParserFn k) (unboxSingleton : Bool) : ParserFn k
| a, c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz unboxSingleton false a c s

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds }

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo :=
{ collectTokens := p.collectTokens ∘ sep.collectTokens,
  collectKinds  := p.collectKinds ∘ sep.collectKinds,
  firstTokens   := p.firstTokens }

@[inline] def sepBy {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) : Parser k :=
{ info := sepByInfo p.info sep.info,
  fn   := sepByFn allowTrailingSep p.fn sep.fn }

@[inline] def sepBy1 {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) (unboxSingleton := false) : Parser k :=
{ info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn unboxSingleton }

@[specialize] partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : BasicParserFn
| c, s =>
  let i := s.pos;
  if c.input.atEnd i then s.mkEOIError
  else if p (c.input.get i) then s.next c.input i
  else s.mkUnexpectedError errorMsg

@[specialize] partial def takeUntilFn (p : Char → Bool) : BasicParserFn
| c, s =>
  let i := s.pos;
  if c.input.atEnd i then s
  else if p (c.input.get i) then s
  else takeUntilFn c (s.next c.input i)

@[specialize] def takeWhileFn (p : Char → Bool) : BasicParserFn :=
takeUntilFn (fun c => !p c)

@[inline] def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : BasicParserFn :=
andthenAux (satisfyFn p errorMsg) (takeWhileFn p)

partial def finishCommentBlock : Nat → BasicParserFn
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
partial def whitespace : BasicParserFn
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
| a, c, s =>
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
@[inline] def rawFn {k : ParserKind} (p : ParserFn k) (trailingWs := false) : ParserFn k
| a, c, s =>
  let startPos := s.pos;
  let s := p a c s;
  if s.hasError then s else rawAux startPos trailingWs a c s

@[inline] def chFn {k : ParserKind} (c : Char) (trailingWs := false) : ParserFn k :=
rawFn (fun _ => satisfyFn (fun d => c == d) ("'" ++ toString c ++ "'")) trailingWs

def rawCh {k : ParserKind} (c : Char) (trailingWs := false) : Parser k :=
{ fn := chFn c trailingWs }

def hexDigitFn : BasicParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    let i    := input.next i;
    if curr.isDigit || ('a' <= curr && curr <= 'f') || ('A' <= curr && curr <= 'F') then s.setPos i
    else s.mkUnexpectedError "invalid hexadecimal numeral"

def quotedCharFn : BasicParserFn
| c, s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else
    let curr := input.get i;
    if curr == '\\' || curr == '\"' || curr == '\'' || curr == 'n' || curr == 't' then
      s.next input i
    else if curr == 'x' then
      andthenAux hexDigitFn hexDigitFn c (s.next input i)
    else if curr == 'u' then
      andthenAux hexDigitFn (andthenAux hexDigitFn (andthenAux hexDigitFn hexDigitFn)) c (s.next input i)
    else
      s.mkUnexpectedError "invalid escape sequence"

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
s.pushSyntax (mkStxLit n val (some info))

def charLitFnAux (startPos : Nat) : BasicParserFn
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

partial def strLitFnAux (startPos : Nat) : BasicParserFn
| c, s =>
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
  let s := takeWhile1Fn (fun c => c == '0' || c == '1') "binary number" c s;
  mkNodeToken numLitKind startPos c s

def octalNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => '0' ≤ c && c ≤ '7') "octal number" c s;
  mkNodeToken numLitKind startPos c s

def hexNumberFn (startPos : Nat) : BasicParserFn :=
fun c s =>
  let s := takeWhile1Fn (fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "hexadecimal number" c s;
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

def mkTokenAndFixPos (startPos : Nat) (tk : Option TokenConfig) : BasicParserFn :=
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

def mkIdResult (startPos : Nat) (tk : Option TokenConfig) (val : Name) : BasicParserFn :=
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

partial def identFnAux (startPos : Nat) (tk : Option TokenConfig) : Name → BasicParserFn
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

private def nameLitAux (startPos : Nat) : BasicParserFn
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

private def tokenFnAux : BasicParserFn
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

/- Treat keywords as identifiers. -/
def rawIdentFn : BasicParserFn :=
fun c s =>
  let input := c.input;
  let i     := s.pos;
  if input.atEnd i then s.mkEOIError
  else identFnAux i none Name.anonymous c s

@[inline] def satisfySymbolFn (p : String → Bool) (expected : List String) : BasicParserFn :=
fun c s =>
  let startPos := s.pos;
  let s        := tokenFn c s;
  if s.hasError then
    s.mkErrorsAt expected startPos
  else
    match s.stxStack.back with
    | Syntax.atom _ sym => if p sym then s else s.mkErrorsAt expected startPos
    | _                 => s.mkErrorsAt expected startPos

@[inline] def symbolFnAux (sym : String) (errorMsg : String) : BasicParserFn :=
satisfySymbolFn (fun s => s == sym) [errorMsg]

def symbolInfo (sym : String) (lbp : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbp := lbp } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbp := lbp } ] }

@[inline] def symbolFn {k : ParserKind} (sym : String) : ParserFn k :=
fun _ => symbolFnAux sym ("'" ++ sym ++ "'")

@[inline] def symbolAux {k : ParserKind} (sym : String) (lbp : Option Nat := none) : Parser k :=
let sym := sym.trim;
{ info := symbolInfo sym lbp,
  fn   := symbolFn sym }

@[inline] def symbol {k : ParserKind} (sym : String) (lbp : Nat) : Parser k :=
symbolAux sym lbp

/-- Check if the following token is the symbol _or_ identifier `sym`. Useful for
    parsing local tokens that have not been added to the token table (but may have
    been so by some unrelated code).

    For example, the universe `max` Function is parsed using this combinator so that
    it can still be used as an identifier outside of universes (but registering it
    as a token in a Term Syntax would not break the universe Parser). -/
def nonReservedSymbolFnAux (sym : String) (errorMsg : String) : BasicParserFn :=
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

@[inline] def nonReservedSymbolFn (sym : String) : BasicParserFn :=
nonReservedSymbolFnAux sym ("'" ++ sym ++ "'")

def nonReservedSymbolInfo (sym : String) (includeIdent : Bool) : ParserInfo :=
{ firstTokens  :=
  if includeIdent then
    FirstTokens.tokens [ { val := sym }, { val := "ident" } ]
  else
    FirstTokens.tokens [ { val := sym } ] }

@[inline] def nonReservedSymbol {k : ParserKind} (sym : String) (includeIdent := false) : Parser k :=
let sym := sym.trim;
{ info := nonReservedSymbolInfo sym includeIdent,
  fn   := fun _ => nonReservedSymbolFn sym }

partial def strAux (sym : String) (errorMsg : String) : Nat → BasicParserFn
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

def checkWsBeforeFn (errorMsg : String) : BasicParserFn :=
fun c s =>
  let prev := s.stxStack.back;
  if checkTailWs prev then s else s.mkError errorMsg

def checkWsBefore {k : ParserKind} (errorMsg : String) : Parser k :=
{ info := epsilonInfo,
  fn   := fun _ => checkWsBeforeFn errorMsg }

def checkTailNoWs (prev : Syntax) : Bool :=
match prev.getTailInfo with
| some info => info.trailing.stopPos == info.trailing.startPos
| none      => false

private def pickNonNone (stack : Array Syntax) : Syntax :=
match stack.findRev? $ fun stx => !stx.isNone with
| none => Syntax.missing
| some stx => stx

def checkNoWsBeforeFn (errorMsg : String) : BasicParserFn :=
fun c s =>
  let prev := pickNonNone s.stxStack;
  if checkTailNoWs prev then s else s.mkError errorMsg

def checkNoWsBefore {k : ParserKind} (errorMsg : String) : Parser k :=
{ info := epsilonInfo,
  fn   := fun _ => checkNoWsBeforeFn errorMsg }

def symbolNoWsInfo (sym : String) (lbpNoWs : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbpNoWs := lbpNoWs } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbpNoWs := lbpNoWs } ] }

@[inline] def symbolNoWsFnAux (sym : String) (errorMsg : String) : ParserFn trailing :=
fun left c s =>
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

@[inline] def symbolNoWsFn (sym : String) : ParserFn trailing :=
symbolNoWsFnAux sym ("'" ++ sym ++ "' without whitespaces around it")

/- Similar to `symbol`, but succeeds only if there is no space whitespace after leading term and after `sym`. -/
@[inline] def symbolNoWsAux (sym : String) (lbp : Option Nat) : TrailingParser :=
let sym := sym.trim;
{ info := symbolNoWsInfo sym lbp,
  fn   := symbolNoWsFn sym }

@[inline] def symbolNoWs (sym : String) (lbp : Nat) : TrailingParser :=
symbolNoWsAux sym lbp

def unicodeSymbolFnAux (sym asciiSym : String) (expected : List String) : BasicParserFn :=
satisfySymbolFn (fun s => s == sym || s == asciiSym) expected

def unicodeSymbolInfo (sym asciiSym : String) (lbp : Option Nat) : ParserInfo :=
{ collectTokens := fun tks => { val := sym, lbp := lbp } :: { val := asciiSym, lbp := lbp } :: tks,
  firstTokens   := FirstTokens.tokens [ { val := sym, lbp := lbp }, { val := asciiSym, lbp := lbp } ] }

@[inline] def unicodeSymbolFn {k : ParserKind} (sym asciiSym : String) : ParserFn k :=
fun _ => unicodeSymbolFnAux sym asciiSym ["'" ++ sym ++ "', '" ++ asciiSym ++ "'"]

@[inline] def unicodeSymbol {k : ParserKind} (sym asciiSym : String) (lbp : Option Nat := none) : Parser k :=
let sym := sym.trim;
let asciiSym := asciiSym.trim;
{ info := unicodeSymbolInfo sym asciiSym lbp,
  fn   := unicodeSymbolFn sym asciiSym }

def unicodeSymbolCheckPrecFnAux (sym asciiSym : String) (lbp : Nat) (expected : List String) (precErrorMsg : String) : ParserFn leading :=
fun (rbp : Nat) c s =>
  if rbp > lbp then s.mkUnexpectedError precErrorMsg
  else satisfySymbolFn (fun s => s == sym || s == asciiSym) expected c s

@[inline] def unicodeSymbolCheckPrecFn (sym asciiSym : String) (lbp : Nat) : ParserFn leading :=
unicodeSymbolCheckPrecFnAux sym asciiSym lbp
  ["'" ++ sym ++ "'", "'" ++ asciiSym ++ "'"]
  ("found '" ++ sym ++ "' as expected, but brackets are needed") -- improve error message

@[inline] def unicodeSymbolCheckPrec (sym asciiSym : String) (lbp : Nat) : Parser leading :=
let sym := sym.trim;
let asciiSym := asciiSym.trim;
{ info := unicodeSymbolInfo sym asciiSym lbp,
  fn   := unicodeSymbolCheckPrecFn sym asciiSym lbp }

def mkAtomicInfo (k : String) : ParserInfo :=
{ firstTokens := FirstTokens.tokens [ { val := k } ] }

def numLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind numLitKind) then s.mkErrorAt "numeral" iniPos else s

@[inline] def numLitNoAntiquot {k : ParserKind} : Parser k :=
{ fn   := numLitFn,
  info := mkAtomicInfo "numLit" }

def strLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "string literal" iniPos else s

@[inline] def strLitNoAntiquot {k : ParserKind} : Parser k :=
{ fn   := strLitFn,
  info := mkAtomicInfo "strLit" }

def charLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind charLitKind) then s.mkErrorAt "character literal" iniPos else s

@[inline] def charLitNoAntiquot {k : ParserKind} : Parser k :=
{ fn   := charLitFn,
  info := mkAtomicInfo "charLit" }

def nameLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind nameLitKind) then s.mkErrorAt "Name literal" iniPos else s

@[inline] def nameLitNoAntiquot {k : ParserKind} : Parser k :=
{ fn   := nameLitFn,
  info := mkAtomicInfo "nameLit" }

def identFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isIdent) then s.mkErrorAt "identifier" iniPos else s

@[inline] def identNoAntiquot {k : ParserKind} : Parser k :=
{ fn   := identFn,
  info := mkAtomicInfo "ident" }

@[inline] def rawIdentNoAntiquot {k : ParserKind} : Parser k :=
{ fn := fun _ => rawIdentFn }

def identEqFn {k : ParserKind} (id : Name) : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError then
    s.mkErrorAt "identifier" iniPos
  else match s.stxStack.back with
    | Syntax.ident _ _ val _ => if val != id then s.mkErrorAt ("expected identifier '" ++ toString id ++ "'") iniPos else s
    | _ => s.mkErrorAt "identifier" iniPos

@[inline] def identEq {k : ParserKind} (id : Name) : Parser k :=
{ fn   := identEqFn id,
  info := mkAtomicInfo "ident" }

def quotedSymbolFn {k : ParserKind} : ParserFn k :=
nodeFn `quotedSymbol (andthenFn (andthenFn (chFn '`') (rawFn (fun _ => takeUntilFn (fun c => c == '`')))) (chFn '`' true))

-- TODO: remove after old frontend is gone
def quotedSymbol {k : ParserKind} : Parser k :=
{ fn := quotedSymbolFn }

def unquotedSymbolFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || s.stxStack.back.isIdent || isLitKind s.stxStack.back.getKind then
    s.mkErrorAt "symbol" iniPos
  else
    s

def unquotedSymbol {k : ParserKind} : Parser k :=
{ fn := unquotedSymbolFn }

instance string2basic {k : ParserKind} : HasCoe String (Parser k) :=
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
  let s           := s.mkLongestNodeAlt prevSize; -- create successful alternative on the top of the stack
  let successNode := s.stxStack.back;
  let s           := s.shrinkStack startSize; -- restore stack to initial size to make sure (failure) nodes are removed from the stack
  s.pushSyntax successNode -- put successNode back on the stack

def longestMatchMkResult (startSize : Nat) (s : ParserState) : ParserState :=
if !s.hasError && s.stackSize > startSize + 1 then s.mkNode choiceKind startSize else s

def longestMatchFnAux {k : ParserKind} (startSize : Nat) (startPos : String.Pos) : List (Parser k) → ParserFn k
| []    => fun _ _ s => longestMatchMkResult startSize s
| p::ps => fun a c s =>
   let s := longestMatchStep startSize startPos p.fn a c s;
   longestMatchFnAux ps a c s

def longestMatchFn₁ {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
let startSize := s.stackSize;
let s := p a c s;
if s.hasError then s else s.mkLongestNodeAlt startSize

def longestMatchFn {k : ParserKind} : List (Parser k) → ParserFn k
| []    => fun _ _ s => s.mkError "longestMatch: empty list"
| [p]   => longestMatchFn₁ p.fn
| p::ps => fun a c s =>
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
| [],    _, _, s => s.mkError "anyOf: empty list"
| [p],   a, c, s => p.fn a c s
| p::ps, a, c, s => orelseFn p.fn (anyOfFn ps) a c s

@[inline] def checkColGeFn (col : Nat) (errorMsg : String) : BasicParserFn :=
fun c s =>
  let pos := c.fileMap.toPosition s.pos;
  if pos.column ≥ col then s
  else s.mkError errorMsg

@[inline] def checkColGe {k : ParserKind} (col : Nat) (errorMsg : String) : Parser k :=
{ fn := fun _ => checkColGeFn col errorMsg }

@[inline] def withPosition {k : ParserKind} (p : Position → Parser k) : Parser k :=
{ info := (p { line := 1, column := 0 }).info,
  fn   := fun a c s =>
   let pos := c.fileMap.toPosition s.pos;
   (p pos).fn a c s }

@[inline] def many1Indent {k : ParserKind} (p : Parser k) (errorMsg : String) : Parser k :=
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

def leadingParser (kind : Name) (tables : PrattParsingTables) (leadingIdentAsSymbol : Bool) : ParserFn leading :=
fun a c s =>
  let iniSz   := s.stackSize;
  let (s, ps) := indexed tables.leadingTable c s leadingIdentAsSymbol;
  let ps      := tables.leadingParsers ++ ps;
  if ps.isEmpty then
    s.mkError (toString kind)
  else
    let s       := longestMatchFn ps a c s;
    mkResult s iniSz

def trailingLoopStep (tables : PrattParsingTables) (ps : List (Parser trailing)) : ParserFn trailing :=
fun left c s =>
  orelseFn (longestMatchFn ps) (anyOfFn tables.trailingParsers) left c s

partial def trailingLoop (tables : PrattParsingTables) (rbp : Nat) (c : ParserContext) : Syntax → ParserState → ParserState
| left, s =>
  let (s, lbp) := currLbp left c s;
  if rbp ≥ lbp then s.pushSyntax left
  else
    let iniSz         := s.stackSize;
    let identAsSymbol := false;
    let (s, ps)       := indexed tables.trailingTable c s identAsSymbol;
    if ps.isEmpty && tables.trailingParsers.isEmpty then
      s.pushSyntax left -- no available trailing parser
    else
      let s := trailingLoopStep tables ps left c s;
      if s.hasError then s
      else
        let s := mkResult s iniSz;
        let left := s.stxStack.back;
        let s    := s.popSyntax;
        trailingLoop left s

def prattParser (kind : Name) (tables : PrattParsingTables) (leadingIdentAsSymbol : Bool) : ParserFn leading :=
fun rbp c s =>
  let s := leadingParser kind tables leadingIdentAsSymbol rbp c s;
  if s.hasError then s
  else
    let left := s.stxStack.back;
    let s    := s.popSyntax;
    trailingLoop tables rbp c left s

abbrev CategoryParserFn := Name → ParserFn leading

def mkCategoryParserFnRef : IO (IO.Ref CategoryParserFn) :=
IO.mkRef $ fun _ _ => whitespace

@[init mkCategoryParserFnRef]
constant categoryParserFnRef : IO.Ref CategoryParserFn := arbitrary _

def mkCategoryParserFnExtension : IO (EnvExtension CategoryParserFn) :=
registerEnvExtension $ categoryParserFnRef.get

@[init mkCategoryParserFnExtension]
def categoryParserFnExtension : EnvExtension CategoryParserFn := arbitrary _

def categoryParserFn (catName : Name) : ParserFn leading :=
fun rbp ctx s => categoryParserFnExtension.getState ctx.env catName rbp ctx s

def categoryParser {k} (catName : Name) (rbp : Nat) : Parser k :=
{ fn := fun _ => categoryParserFn catName rbp }

-- Define `termParser` here because we need it for antiquotations
@[inline] def termParser {k : ParserKind} (rbp : Nat := 0) : Parser k :=
categoryParser `term rbp

/- ============== -/
/- Antiquotations -/
/- ============== -/

def dollarSymbol {k : ParserKind} : Parser k := symbol "$" 1

/-- Fail if previous token is immediately followed by ':'. -/
private def noImmediateColon {k : ParserKind} : Parser k :=
{ fn := fun _ c s =>
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

def setExpectedFn {k : ParserKind} (expected : List String) (p : ParserFn k) : ParserFn k :=
fun a c s => match p a c s with
  | s'@{ errorMsg := some msg } => { s' with errorMsg := some { msg with expected := [] } }
  | s'                          => s'

def setExpected {k : ParserKind} (expected : List String) (p : Parser k) : Parser k :=
{ fn := setExpectedFn expected p.fn, info := p.info }

def pushNone {k : ParserKind} : Parser k :=
{ fn := fun a c s => s.pushSyntax mkNullNode }

/-
  We support two kinds of antiquotations: `$id` and `$(t)`, where `id` is a term identifier and `t` is a term.

  TODO: we are making both cases look like syntax terms. Reason: the current expander expects a term.
  We should remove this hack and modify the expander. This hack is bad since it relies on how we define `id` and `paren` in
  the term parser at `Term.lean`. -/
private def antiquotId {k} : Parser k         := node `Lean.Parser.Term.id (identNoAntiquot >> pushNone)
private def antiquotNestedExpr {k} : Parser k := node `Lean.Parser.Term.paren ("(" >> node nullKind (termParser >> pushNone) >> ")")
private def antiquotExpr {k} : Parser k       := antiquotId <|> antiquotNestedExpr

/--
  Define parser for `$e` (if anonymous == true) and `$e:name`. Both
  forms can also be used with an appended `*` to turn them into an
  antiquotation "splice". If `kind` is given, it will additionally be checked
  when evaluating `match_syntax`. -/
def mkAntiquot {k : ParserKind} (name : String) (kind : Option SyntaxNodeKind) (anonymous := true) : Parser k :=
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

def nodeWithAntiquot {k : ParserKind} (name : String) (kind : SyntaxNodeKind) (p : Parser k) : Parser k :=
mkAntiquot name kind false <|> node kind p

def ident {k : ParserKind} : Parser k :=
mkAntiquot "ident" identKind <|> identNoAntiquot

-- `ident` and `rawIdent` produce the same syntax tree, so we reuse the antiquotation kind name
def rawIdent {k : ParserKind} : Parser k :=
mkAntiquot "ident" identKind <|> rawIdentNoAntiquot

def numLit {k : ParserKind} : Parser k :=
mkAntiquot "numLit" numLitKind <|> numLitNoAntiquot

def strLit {k : ParserKind} : Parser k :=
mkAntiquot "strLit" strLitKind <|> strLitNoAntiquot

def charLit {k : ParserKind} : Parser k :=
mkAntiquot "charLit" charLitKind <|> charLitNoAntiquot

def nameLit {k : ParserKind} : Parser k :=
mkAntiquot "nameLit" nameLitKind <|> nameLitNoAntiquot

def categoryParserOfStackFn (offset : Nat) : ParserFn leading :=
fun rbp ctx s =>
  let stack := s.stxStack;
  if stack.size < offset + 1 then
    s.mkUnexpectedError ("failed to determine parser category using syntax stack, stack is too small")
  else
    match stack.get! (stack.size - offset - 1) with
    | Syntax.ident _ _ catName _ => categoryParserFn catName rbp ctx s
    | _ => s.mkUnexpectedError ("failed to determine parser category using syntax stack, the specified element on the stack is not an identifier")

def categoryParserOfStack {k} (offset : Nat) (rbp : Nat := 0) : Parser k :=
{ fn := fun _ => categoryParserOfStackFn offset rbp }

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
| parser    (catName : Name) (declName : Name) (k : ParserKind) (p : Parser k) : ParserExtensionEntry

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

def addParser {k} (categories : ParserCategories) (catName : Name) (declName : Name) (p : Parser k) : Except String ParserCategories :=
match k, p with
| leading, p  => addLeadingParser categories catName declName p
| trailing, p => addTrailingParser categories catName p

def addParserTokens (tokenTable : TokenTable) (info : ParserInfo) : Except String TokenTable :=
let newTokens := info.collectTokens [];
newTokens.foldlM addTokenConfig tokenTable

private def updateBuiltinTokens (info : ParserInfo) (declName : Name) : IO Unit := do
tokenTable ← builtinTokenTable.swap {};
match addParserTokens tokenTable info with
| Except.ok tokenTable => builtinTokenTable.set tokenTable
| Except.error msg     => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', " ++ msg))

def addBuiltinParser {k} (catName : Name) (declName : Name) (p : Parser k) : IO Unit := do
categories ← builtinParserCategoriesRef.get;
categories ← IO.ofExcept $ addParser categories catName declName p;
builtinParserCategoriesRef.set categories;
builtinSyntaxNodeKindSetRef.modify p.info.collectKinds;
updateBuiltinTokens p.info declName

def addBuiltinLeadingParser (catName : Name) (declName : Name) (p : Parser) : IO Unit :=
addBuiltinParser catName declName p

def addBuiltinTrailingParser (catName : Name) (declName : Name) (p : TrailingParser) : IO Unit :=
addBuiltinParser catName declName p

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
| ParserExtensionEntry.parser catName declName _ parser =>
  match addParser s.categories catName declName parser with
  | Except.ok categories => { categories := categories, newEntries := ParserExtensionOleanEntry.parser catName declName :: s.newEntries, .. s }
  | _ => unreachable!

def compileParserDescr (categories : ParserCategories) : forall {k : ParserKind}, ParserDescrCore k → Except String (Parser k)
| _, ParserDescr.andthen d₁ d₂                       => andthen <$> compileParserDescr d₁ <*> compileParserDescr d₂
| _, ParserDescr.orelse d₁ d₂                        => orelse <$> compileParserDescr d₁ <*> compileParserDescr d₂
| _, ParserDescr.optional d                          => optional <$> compileParserDescr d
| _, ParserDescr.lookahead d                         => lookahead <$> compileParserDescr d
| _, ParserDescr.try d                               => try <$> compileParserDescr d
| _, ParserDescr.many d                              => many <$> compileParserDescr d
| _, ParserDescr.many1 d                             => many1 <$> compileParserDescr d
| _, ParserDescr.sepBy d₁ d₂                         => sepBy <$> compileParserDescr d₁ <*> compileParserDescr d₂
| _, ParserDescr.sepBy1 d₁ d₂                        => sepBy1 <$> compileParserDescr d₁ <*> compileParserDescr d₂
| _, ParserDescr.node k d                            => node k <$> compileParserDescr d
| _, ParserDescr.symbol tk lbp                       => pure $ symbolAux tk lbp
| _, ParserDescr.numLit                              => pure $ numLit
| _, ParserDescr.strLit                              => pure $ strLit
| _, ParserDescr.charLit                             => pure $ charLit
| _, ParserDescr.nameLit                             => pure $ nameLit
| _, ParserDescr.ident                               => pure $ ident
| ParserKind.leading,
  ParserDescr.nonReservedSymbol tk includeIdent      => pure $ nonReservedSymbol tk includeIdent
| _, ParserDescr.parser catName rbp =>
  match categories.find? catName with
  | some _ => pure $ categoryParser catName rbp
  | none   => throwUnknownParserCategory catName
| ParserKind.trailing, ParserDescr.pushLeading => pure $ pushLeading

unsafe def mkParserOfConstantUnsafe (env : Environment) (categories : ParserCategories) (constName : Name)
    : Except String (Sigma (fun (k : ParserKind) => Parser k)) :=
match env.find? constName with
| none      => throw ("unknow constant '" ++ toString constName ++ "'")
| some info =>
  match info.type with
  | Expr.const `Lean.Parser.TrailingParser _ _ => do
    p ← env.evalConst (Parser trailing) constName;
    pure ⟨trailing, p⟩
  | Expr.app (Expr.const `Lean.Parser.Parser _ _) (Expr.const `Lean.ParserKind.leading _ _) _ => do
    p ← env.evalConst (Parser leading) constName;
    pure ⟨leading, p⟩
  | Expr.const `Lean.ParserDescr _ _ => do
    d ← env.evalConst ParserDescr constName;
    p ← compileParserDescr categories d;
    pure ⟨leading, p⟩
  | Expr.const `Lean.TrailingParserDescr _ _ => do
    d ← env.evalConst TrailingParserDescr constName;
    p ← compileParserDescr categories d;
    pure ⟨trailing, p⟩
  | _ => throw ("unexpected parser type at '" ++ toString constName ++ "' (`ParserDescr`, `TrailingParserDescr`, `Parser` or `TrailingParser` expected")

@[implementedBy mkParserOfConstantUnsafe]
constant mkParserOfConstant (env : Environment) (categories : ParserCategories) (constName : Name) : Except String (Sigma (fun (k : ParserKind) => Parser k)) :=
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
          match addParser s.categories catName declName p.2 with
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

def categoryParserFnImplAux (catName : Name) : ParserFn leading :=
fun rbp ctx s =>
  let categories := (parserExtension.getState ctx.env).categories;
  match categories.find? catName with
  | some cat => prattParser catName cat.tables cat.leadingIdentAsSymbol rbp ctx s
  | none     => s.mkUnexpectedError ("unknown parser category '" ++ toString catName ++ "'")

private def catNameToString : Name → String
| Name.str Name.anonymous s _ => s
| n                           => n.toString

def categoryParserFnImpl (catName : Name) : ParserFn leading :=
if catName != `term then
  orelseFn (mkAntiquot (catNameToString catName) none false).fn (categoryParserFnImplAux catName)
else
  categoryParserFnImplAux catName

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
{ toInputContext := ctx,
  env            := env,
  tokens         := getTokenTable env }

def mkParserState (input : String) : ParserState :=
{ cache := initCacheForInput input }

def runParserCategory (env : Environment) (catName : Name) (input : String) (fileName := "<input>") : Except String Syntax :=
let categories := (parserExtension.getState env).categories;
match categories.find? catName with
| some cat =>
  let c := mkParserContext env (mkInputContext input fileName);
  let s := mkParserState input;
  let s := whitespace c s;
  let s := prattParser catName cat.tables cat.leadingIdentAsSymbol (0 : Nat) c s;
  if s.hasError then
    Except.error (s.toErrorMsg c)
  else
    Except.ok s.stxStack.back
| none => throwUnknownParserCategory catName

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
 | Expr.app (Expr.const `Lean.Parser.Parser _ _) (Expr.const `Lean.ParserKind.leading _ _) _ =>
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
  let parserKind := p.1;
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
  match addParser categories catName declName parser with
  | Except.ok _     => pure $ parserExtension.addEntry env $ ParserExtensionEntry.parser catName declName parserKind parser
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

def fieldIdxFn : BasicParserFn :=
fun c s =>
  let iniPos := s.pos;
  let curr     := c.input.get iniPos;
  if curr.isDigit && curr != '0' then
    let s     := takeWhileFn (fun c => c.isDigit) c s;
    mkNodeToken fieldIdxKind iniPos c s
  else
    s.mkErrorAt "field index" iniPos

@[inline] def fieldIdx {k : ParserKind} : Parser k :=
mkAntiquot "fieldIdx" `fieldIdx <|>
{ fn   := fun _ => fieldIdxFn,
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
