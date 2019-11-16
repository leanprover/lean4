/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Position
import Init.Lean.Syntax
import Init.Lean.ToExpr
import Init.Lean.Message
import Init.Lean.Environment
import Init.Lean.Attributes
import Init.Lean.Parser.Trie
import Init.Lean.Parser.Identifier
import Init.Lean.Compiler.InitAttr

namespace Lean
namespace Parser

abbrev mkAtom (info : SourceInfo) (val : String) : Syntax :=
Syntax.atom info val

abbrev mkIdent (info : SourceInfo) (rawVal : Substring) (val : Name) : Syntax :=
Syntax.ident (some info) rawVal val []

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

abbrev SyntaxNodeKindSet := HashMap SyntaxNodeKind Unit

structure ParserContextCore :=
(input    : String)
(fileName : String)
(fileMap  : FileMap)
(tokens   : TokenTable)

instance ParserContextCore.inhabited : Inhabited ParserContextCore :=
⟨{ input := "", fileName := "", fileMap := arbitrary _, tokens := {} }⟩

structure ParserContext extends ParserContextCore :=
(env      : Environment)

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

inductive ParserKind
| leading | trailing

export ParserKind (leading trailing)

def ParserArg : ParserKind → Type
| ParserKind.leading => Nat
| ParserKind.trailing => Syntax

def BasicParserFn := ParserContext → ParserState → ParserState

def ParserFn (k : ParserKind) := ParserArg k → BasicParserFn

instance ParserFn.inhabited (k : ParserKind) : Inhabited (ParserFn k) := ⟨fun _ _ => id⟩

inductive FirstTokens
| epsilon   : FirstTokens
| unknown   : FirstTokens
| tokens    : List TokenConfig → FirstTokens
| optTokens : List TokenConfig → FirstTokens

namespace FirstTokens

def merge : FirstTokens → FirstTokens → FirstTokens
| epsilon,      tks          => tks
| tks,          epsilon      => tks
| tokens s₁,    tokens s₂    => tokens (s₁ ++ s₂)
| optTokens s₁, optTokens s₂ => optTokens (s₁ ++ s₂)
| tokens s₁,    optTokens s₂ => tokens (s₁ ++ s₂)
| optTokens s₁, tokens s₂    => tokens (s₁ ++ s₂)
| _,            _            => unknown

def seq : FirstTokens → FirstTokens → FirstTokens
| epsilon,      tks          => tks
| optTokens s₁, optTokens s₂ => optTokens (s₁ ++ s₂)
| optTokens s₁, tokens s₂    => tokens (s₁ ++ s₂)
| tks,          _            => tks

def toOptional : FirstTokens → FirstTokens
| tokens tks => optTokens tks
| tks        => tks

def toStr : FirstTokens → String
| epsilon       => "epsilon"
| unknown       => "unknown"
| tokens tks    => toString tks
| optTokens tks => "?" ++ toString tks

instance : HasToString FirstTokens := ⟨toStr⟩

end FirstTokens

structure ParserInfo :=
(updateTokens  : TokenTable → ExceptT String Id TokenTable := fun tks => pure tks)
(updateKindSet : SyntaxNodeKindSet → SyntaxNodeKindSet     := id)
(firstTokens   : FirstTokens                               := FirstTokens.unknown)

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
{ updateTokens  := fun tks => q.updateTokens tks >>= p.updateTokens,
  updateKindSet := p.updateKindSet ∘ q.updateKindSet,
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
{ updateTokens  := p.updateTokens,
  updateKindSet := fun s => s.insert n (),
  firstTokens   := p.firstTokens }

@[inline] def node {k : ParserKind} (n : SyntaxNodeKind) (p : Parser k) : Parser k :=
{ info := nodeInfo n p.info,
  /- Remark: the compiler currently does not eta-expand structure fields.
     So, we force it here to trigger inlining at `node` combinators. -/
  fn   := nodeFn n p.fn }

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
{ updateTokens  := fun tks => q.updateTokens tks >>= p.updateTokens,
  updateKindSet := p.updateKindSet ∘ q.updateKindSet,
  firstTokens   := p.firstTokens.merge q.firstTokens }

@[inline] def orelse {k : ParserKind} (p q : Parser k) : Parser k :=
{ info := orelseInfo p.info q.info,
  fn   := orelseFn p.fn q.fn }

instance hashOrelse {k : ParserKind} : HasOrelse (Parser k) :=
⟨orelse⟩

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ updateTokens  := info.updateTokens,
  updateKindSet := info.updateKindSet }

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
{ updateTokens  := p.updateTokens,
  updateKindSet := p.updateKindSet,
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

@[inline] def many1Fn {k : ParserKind} (p : ParserFn k) : ParserFn k :=
fun a c s =>
  let iniSz  := s.stackSize;
  let s := andthenFn p (manyAux p) a c s;
  s.mkNode nullKind iniSz

@[inline] def many1 {k : ParserKind} (p : Parser k) : Parser k :=
{ info := p.info,
  fn   := many1Fn p.fn }

@[specialize] private partial def sepByFnAux {k : ParserKind} (p : ParserFn k) (sep : ParserFn k) (allowTrailingSep : Bool) (iniSz : Nat) : Bool → ParserFn k
| pOpt, a, c, s =>
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
| a, c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz true a c s

@[specialize] def sepBy1Fn {k : ParserKind} (allowTrailingSep : Bool) (p : ParserFn k) (sep : ParserFn k) : ParserFn k
| a, c, s =>
  let iniSz := s.stackSize;
  sepByFnAux p sep allowTrailingSep iniSz false a c s

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo :=
{ updateTokens  := fun tks => p.updateTokens tks >>= sep.updateTokens,
  updateKindSet := p.updateKindSet ∘ sep.updateKindSet }

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo :=
{ updateTokens  := fun tks => p.updateTokens tks >>= sep.updateTokens,
  updateKindSet := p.updateKindSet ∘ sep.updateKindSet,
  firstTokens   := p.firstTokens }

@[inline] def sepBy {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) : Parser k :=
{ info := sepByInfo p.info sep.info,
  fn   := sepByFn allowTrailingSep p.fn sep.fn }

@[inline] def sepBy1 {k : ParserKind} (p sep : Parser k) (allowTrailingSep : Bool := false) : Parser k :=
{ info := sepBy1Info p.info sep.info,
  fn   := sepBy1Fn allowTrailingSep p.fn sep.fn }

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
        mkIdResult startPos tk r c s
    else
      mkTokenAndFixPos startPos tk c s

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

def insertToken (sym : String) (lbp : Option Nat) (tks : TokenTable) : ExceptT String Id TokenTable :=
if sym == "" then throw "invalid empty symbol"
else match tks.find sym, lbp with
| none,       _           => pure (tks.insert sym { val := sym, lbp := lbp })
| some _,     none        => pure tks
| some tk,    some newLbp =>
  match tk.lbp with
  | none        => pure (tks.insert sym { lbp := lbp, .. tk })
  | some oldLbp => if newLbp == oldLbp then pure tks else throw ("precedence mismatch for '" ++ toString sym ++ "', previous: " ++ toString oldLbp ++ ", new: " ++ toString newLbp)

def symbolInfo (sym : String) (lbp : Option Nat) : ParserInfo :=
{ updateTokens := insertToken sym lbp,
  firstTokens  := FirstTokens.tokens [ { val := sym, lbp := lbp } ] }

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
def symbolOrIdentFnAux (sym : String) (errorMsg : String) : BasicParserFn :=
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

@[inline] def symbolOrIdentFn (sym : String) : BasicParserFn :=
symbolOrIdentFnAux sym ("'" ++ sym ++ "'")

def symbolOrIdentInfo (sym : String) : ParserInfo :=
{ firstTokens  := FirstTokens.tokens [ { val := sym }, { val := "ident" } ] }

@[inline] def symbolOrIdent {k : ParserKind} (sym : String) : Parser k :=
let sym := sym.trim;
{ info := symbolOrIdentInfo sym,
  fn   := fun _ => symbolOrIdentFn sym }

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

def checkNoWsBeforeFn (errorMsg : String) : BasicParserFn :=
fun c s =>
  let prev := s.stxStack.back;
  if checkTailNoWs prev then s else s.mkError errorMsg

def checkNoWsBefore {k : ParserKind} (errorMsg : String) : Parser k :=
{ info := epsilonInfo,
  fn   := fun _ => checkNoWsBeforeFn errorMsg }

def insertNoWsToken (sym : String) (lbpNoWs : Option Nat) (tks : TokenTable) : ExceptT String Id TokenTable :=
if sym == "" then throw "invalid empty symbol"
else match tks.find sym, lbpNoWs with
| none,       _           => pure (tks.insert sym { val := sym, lbpNoWs := lbpNoWs })
| some _,     none        => pure tks
| some tk,    some newLbp =>
  match tk.lbpNoWs with
  | none        => pure (tks.insert sym { lbpNoWs := lbpNoWs, .. tk })
  | some oldLbp => if newLbp == oldLbp then pure tks else throw ("(no whitespace) precedence mismatch for '" ++ toString sym ++ "', previous: " ++ toString oldLbp ++ ", new: " ++ toString newLbp)

def symbolNoWsInfo (sym : String) (lbpNoWs : Option Nat) : ParserInfo :=
{ updateTokens := insertNoWsToken sym lbpNoWs,
  firstTokens  := FirstTokens.tokens [ { val := sym, lbpNoWs := lbpNoWs } ] }

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
{ updateTokens := fun tks => insertToken sym lbp tks >>= insertToken asciiSym lbp,
  firstTokens  := FirstTokens.tokens [ { val := sym, lbp := lbp }, { val := asciiSym, lbp := lbp } ] }

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

@[inline] def numLit {k : ParserKind} : Parser k :=
{ fn   := numLitFn,
  info := mkAtomicInfo "numLit" }

def strLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind strLitKind) then s.mkErrorAt "string literal" iniPos else s

@[inline] def strLit {k : ParserKind} : Parser k :=
{ fn   := strLitFn,
  info := mkAtomicInfo "strLit" }

def charLitFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isOfKind charLitKind) then s.mkErrorAt "character literal" iniPos else s

@[inline] def charLit {k : ParserKind} : Parser k :=
{ fn   := charLitFn,
  info := mkAtomicInfo "charLit" }

def identFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || !(s.stxStack.back.isIdent) then s.mkErrorAt "identifier" iniPos else s

@[inline] def ident {k : ParserKind} : Parser k :=
{ fn   := identFn,
  info := mkAtomicInfo "ident" }

@[inline] def rawIdent {k : ParserKind} : Parser k :=
{ fn := fun _ => rawIdentFn }

def quotedSymbolFn {k : ParserKind} : ParserFn k :=
nodeFn `quotedSymbol (andthenFn (andthenFn (chFn '`') (rawFn (fun _ => takeUntilFn (fun c => c == '`')))) (chFn '`' true))

def quotedSymbol {k : ParserKind} : Parser k :=
{ fn := quotedSymbolFn }

def unquotedSymbolFn {k : ParserKind} : ParserFn k :=
fun _ c s =>
  let iniPos := s.pos;
  let s      := tokenFn c s;
  if s.hasError || s.stxStack.back.isIdent || s.stxStack.back.isOfKind strLitKind || s.stxStack.back.isOfKind charLitKind || s.stxStack.back.isOfKind numLitKind then
    s.mkErrorAt "symbol" iniPos
  else
    s

def unquotedSymbol {k : ParserKind} : Parser k :=
{ fn := unquotedSymbolFn }

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
{ fn   := fun _ => fieldIdxFn,
  info := mkAtomicInfo "fieldIdx" }

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
  s.mkLongestNodeAlt startSize

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

structure ParsingTables :=
(leadingTable    : TokenMap Parser := {})
(trailingTable   : TokenMap TrailingParser := {})
(trailingParsers : List TrailingParser := []) -- for supporting parsers such as function application

instance ParsingTables.inhabited : Inhabited ParsingTables := ⟨{}⟩

def currLbp (left : Syntax) (c : ParserContext) (s : ParserState) : ParserState × Nat :=
let (s, stx) := peekToken c s;
match stx with
| some (Syntax.atom _ sym) =>
  match c.tokens.matchPrefix sym 0 with
  | (_, some tk) => match tk.lbp, tk.lbpNoWs with
    | some lbp, none         => (s, lbp)
    | none, some lbpNoWs     => (s, lbpNoWs)
    | some lbp, some lbpNoWs => if checkTailNoWs left then (s, lbpNoWs) else (s, lbp)
    | none, none             => (s, 0)
  | _            => (s, 0)
| some (Syntax.ident _ _ _ _) => (s, appPrec)
-- TODO(Leo): add support for associating lbp with syntax node kinds.
| some (Syntax.node k _)      => if k == numLitKind || k == charLitKind || k == strLitKind || k == fieldIdxKind then (s, appPrec) else (s, 0)
| _                           => (s, 0)

def indexed {α : Type} (map : TokenMap α) (c : ParserContext) (s : ParserState) : ParserState × List α :=
let (s, stx) := peekToken c s;
let find (n : Name) : ParserState × List α :=
  match map.find n with
  | some as => (s, as)
  | _       => (s, []);
match stx with
| some (Syntax.atom _ sym)    => find (mkSimpleName sym)
| some (Syntax.ident _ _ _ _) => find `ident
| some (Syntax.node k _)      => find k
| _                           => (s, [])

private def mkResult (s : ParserState) (iniSz : Nat) : ParserState :=
if s.stackSize == iniSz + 1 then s
else s.mkNode nullKind iniSz -- throw error instead?

def leadingParser (kind : String) (tables : ParsingTables) : ParserFn leading :=
fun a c s =>
  let iniSz   := s.stackSize;
  let (s, ps) := indexed tables.leadingTable c s;
  if ps.isEmpty then
    s.mkError kind
  else
    let s       := longestMatchFn ps a c s;
    mkResult s iniSz

def trailingLoopStep (tables : ParsingTables) (ps : List (Parser trailing)) : ParserFn trailing :=
fun left c s =>
  orelseFn (longestMatchFn ps) (anyOfFn tables.trailingParsers) left c s

partial def trailingLoop (tables : ParsingTables) (rbp : Nat) (c : ParserContext) : Syntax → ParserState → ParserState
| left, s =>
  let (s, lbp) := currLbp left c s;
  if rbp ≥ lbp then s.pushSyntax left
  else
    let iniSz   := s.stackSize;
    let (s, ps) := indexed tables.trailingTable c s;
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

def prattParser (kind : String) (tables : ParsingTables) : ParserFn leading :=
fun rbp c s =>
  let s := leadingParser kind tables rbp c s;
  if s.hasError then s
  else
    let left := s.stxStack.back;
    let s    := s.popSyntax;
    trailingLoop tables rbp c left s

def mkBuiltinTokenTable : IO (IO.Ref TokenTable) :=
IO.mkRef {}

@[init mkBuiltinTokenTable]
constant builtinTokenTable : IO.Ref TokenTable := arbitrary _

def mkImportedTokenTable (es : Array (Array TokenConfig)) : IO TokenTable :=
do table ← builtinTokenTable.get;
   -- TODO: add `es` to `table`
   pure table

/- We use a TokenTable attribute to make sure they are scoped.
   Users do not directly use this attribute. They use them indirectly when
   they use parser attributes. -/
structure TokenTableAttribute :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension TokenConfig TokenTable)

instance TokenTableAttribute.inhabited : Inhabited TokenTableAttribute := ⟨{ attr := arbitrary _, ext := arbitrary _ }⟩

section
set_option compiler.extract_closed false
def mkTokenTableAttribute : IO TokenTableAttribute :=
do ext : PersistentEnvExtension TokenConfig TokenTable ← registerPersistentEnvExtension {
     name            := `_tokens_,
     addImportedFn   := fun es => mkImportedTokenTable es,
     addEntryFn      := fun (s : TokenTable) _ => s,         -- TODO
     exportEntriesFn := fun _ => #[],                        -- TODO
     statsFn         := fun _ => fmt "token table attribute" -- TODO
   };
   let attrImpl : AttributeImpl := {
     name  := `_tokens_,
     descr := "internal token table attribute",
     add   := fun env decl args persistent => pure env -- TODO
   };
   pure { ext := ext, attr := attrImpl }
end

@[init mkTokenTableAttribute]
constant tokenTableAttribute : TokenTableAttribute := arbitrary _

/- Global table with all SyntaxNodeKind's -/
def mkSyntaxNodeKindSetRef : IO (IO.Ref SyntaxNodeKindSet) := IO.mkRef {}
@[init mkSyntaxNodeKindSetRef]
constant syntaxNodeKindSetRef : IO.Ref SyntaxNodeKindSet := arbitrary _

def updateSyntaxNodeKinds (pinfo : ParserInfo) : IO Unit :=
syntaxNodeKindSetRef.modify pinfo.updateKindSet

def isValidSyntaxNodeKind (k : SyntaxNodeKind) : IO Bool :=
do s ← syntaxNodeKindSetRef.get;
   pure $ s.contains k

def getSyntaxNodeKinds : IO (List SyntaxNodeKind) :=
do s ← syntaxNodeKindSetRef.get;
   pure $ s.fold (fun ks k _ => k::ks) []

def mkParserContextCore (env : Environment) (input : String) (fileName : String) : ParserContextCore :=
{ input    := input,
  fileName := fileName,
  fileMap  := input.toFileMap,
  tokens   := tokenTableAttribute.ext.getState env }

@[inline] def ParserContextCore.toParserContext (env : Environment) (ctx : ParserContextCore) : ParserContext :=
{ env := env, toParserContextCore := ctx }

def mkParserContext (env : Environment) (input : String) (fileName : String) : ParserContext :=
(mkParserContextCore env input fileName).toParserContext env

def mkParserState (input : String) : ParserState :=
{ cache := initCacheForInput input }

def runParser (env : Environment) (tables : ParsingTables) (input : String) (fileName := "<input>") (kind := "<main>") : Except String Syntax :=
let c := mkParserContext env input fileName;
let s := mkParserState input;
let s := whitespace c s;
let s := prattParser kind tables (0 : Nat) c s;
if s.hasError then
  Except.error (s.toErrorMsg c)
else
  Except.ok s.stxStack.back

def mkBuiltinParsingTablesRef : IO (IO.Ref ParsingTables) :=
IO.mkRef {}

private def updateTokens (info : ParserInfo) (declName : Name) : IO Unit :=
do tokens ← builtinTokenTable.swap {};
   match info.updateTokens tokens with
   | Except.ok newTokens => builtinTokenTable.set newTokens
   | Except.error msg    => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', " ++ msg))

def addBuiltinLeadingParser (tablesRef : IO.Ref ParsingTables) (declName : Name) (p : Parser) : IO Unit :=
do tables ← tablesRef.get;
   tablesRef.reset;
   updateTokens p.info declName;
   updateSyntaxNodeKinds p.info;
   let addTokens (tks : List TokenConfig) : IO Unit :=
     let tks := tks.map $ fun tk => mkSimpleName tk.val;
     tablesRef.set $ tks.eraseDups.foldl (fun (tables : ParsingTables) tk => { leadingTable := tables.leadingTable.insert tk p, .. tables }) tables;
   match p.info.firstTokens with
   | FirstTokens.tokens tks    => addTokens tks
   | FirstTokens.optTokens tks => addTokens tks
   | _ => throw (IO.userError ("invalid builtin parser '" ++ toString declName ++ "', initial token is not statically known"))

def addBuiltinTrailingParser (tablesRef : IO.Ref ParsingTables) (declName : Name) (p : TrailingParser) : IO Unit :=
do tables ← tablesRef.get;
   tablesRef.reset;
   updateTokens p.info declName;
   updateSyntaxNodeKinds p.info;
   let addTokens (tks : List TokenConfig) : IO Unit :=
     let tks := tks.map $ fun tk => mkSimpleName tk.val;
     tablesRef.set $ tks.eraseDups.foldl (fun (tables : ParsingTables) tk => { trailingTable := tables.trailingTable.insert tk p, .. tables }) tables;
   match p.info.firstTokens with
   | FirstTokens.tokens tks    => addTokens tks
   | FirstTokens.optTokens tks => addTokens tks
   | _ => tablesRef.set { trailingParsers := p :: tables.trailingParsers, .. tables }

def declareBuiltinParser (env : Environment) (addFnName : Name) (refDeclName : Name) (declName : Name) : IO Environment :=
let name := `_regBuiltinParser ++ declName;
let type := mkApp (mkConst `IO) (mkConst `Unit);
let val  := mkCAppN addFnName #[mkConst refDeclName, toExpr declName, mkConst declName];
let decl := Declaration.defnDecl { name := name, lparams := [], type := type, value := val, hints := ReducibilityHints.opaque, isUnsafe := false };
match env.addAndCompile {} decl with
-- TODO: pretty print error
| Except.error _ => throw (IO.userError ("failed to emit registration code for builtin parser '" ++ toString declName ++ "'"))
| Except.ok env  => IO.ofExcept (setInitAttr env name)

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
     | Expr.const `Lean.Parser.TrailingParser _ _ =>
       declareTrailingBuiltinParser env refDeclName declName
     | Expr.app (Expr.const `Lean.Parser.Parser _ _) (Expr.const `Lean.Parser.ParserKind.leading _ _) _ =>
       declareLeadingBuiltinParser env refDeclName declName
     | _ =>
       throw (IO.userError ("unexpected parser type at '" ++ toString declName ++ "' (`Parser` or `TrailingParser` expected"))
 },
 applicationTime := AttributeApplicationTime.afterCompilation
}

@[noinline] unsafe def runBuiltinParserUnsafe (kind : String) (ref : IO.Ref ParsingTables) : ParserFn leading :=
fun a c s =>
match unsafeIO (do tables ← ref.get; pure $ prattParser kind tables a c s) with
| Except.ok s => s
| _           => s.mkError "failed to access builtin reference"

@[implementedBy runBuiltinParserUnsafe]
constant runBuiltinParser (kind : String) (ref : IO.Ref ParsingTables) : ParserFn leading := arbitrary _

inductive ParserAttributeEntry
| leading (n : Name)
| trailing (n : Name)

structure ParserAttribute :=
(attr : AttributeImpl)
(ext  : PersistentEnvExtension ParserAttributeEntry ParsingTables)
(kind : String)

instance ParserAttribute.inhabited : Inhabited ParserAttribute := ⟨{ attr := arbitrary _, ext := arbitrary _, kind := "" }⟩

/-
This is just the basic skeleton where we create an
extensible/scoped parser attribute that is optionally initialized with
a builtin parser attribute.

The current implementation just uses the bultin parser.
We still need to:
- Add a ParserDescr type, and write an interpreter for it.
- Add support for scoped parser extensions.
-/
def registerParserAttribute (attrName : Name) (kind : String) (descr : String) (builtinTable : Option (IO.Ref ParsingTables) := none) : IO ParserAttribute :=
do ext : PersistentEnvExtension ParserAttributeEntry ParsingTables ← registerPersistentEnvExtension {
     name            := attrName,
     addImportedFn   := fun es => do
       table ← match builtinTable with
       | some table => table.get
       | none       => pure {};
    -- TODO: populate table with `es`
       pure table,
     addEntryFn      := fun (s : ParsingTables) _ => s, -- TODO
     exportEntriesFn := fun _ => #[],                   -- TODO
     statsFn         := fun _ => fmt "parser attribute" -- TODO
   };
   let attrImpl : AttributeImpl := {
     name  := attrName,
     descr := descr,
     add   := fun env decl args persistent => pure env -- TODO
   };
   pure { ext := ext, attr := attrImpl, kind := kind }

namespace ParserAttribute

def runParser (attr : ParserAttribute) : ParserFn leading :=
fun a c s =>
  let tables : ParsingTables := attr.ext.getState c.env;
  prattParser attr.kind tables a c s

end ParserAttribute

end Parser

namespace Syntax

def isNone {α} (stx : Syntax α) : Bool :=
stx.ifNode (fun n => n.getKind == nullKind && n.getNumArgs == 0) (fun n => false)

def getOptional {α} (s : Syntax α) : Option (Syntax α) :=
s.ifNode
  (fun n => if n.getKind == nullKind && n.getNumArgs == 1 then some (n.getArg 0) else none)
  (fun _ => none)

def getOptionalIdent {α} (stx : Syntax α) : Option Name :=
match stx.getOptional with
| some stx => some stx.getId
| none     => none

section
variables {α β : Type} {m : Type → Type} [Monad m]

@[specialize] partial def mfoldArgsAux (delta : Nat) (s : Array (Syntax α)) (f : Syntax α → β → m β) : Nat → β → m β
| i, b =>
  if h : i < s.size then do
    let curr := s.get ⟨i, h⟩;
    b ← f curr b;
    mfoldArgsAux (i+delta) b
  else
    pure b

@[inline] def mfoldArgs (s : Syntax α) (f : Syntax α → β → m β) (b : β) : m β :=
mfoldArgsAux 1 s.getArgs f 0 b

@[inline] def foldArgs (s : Syntax α) (f : Syntax α → β → β) (b : β) : β :=
Id.run (s.mfoldArgs f b)

@[inline] def mforArgs (s : Syntax α) (f : Syntax α → m Unit) : m Unit :=
s.mfoldArgs (fun s _ => f s) ()

@[inline] def mfoldSepArgs (s : Syntax α) (f : Syntax α → β → m β) (b : β) : m β :=
mfoldArgsAux 2 s.getArgs f 0 b

@[inline] def foldSepArgs (s : Syntax α) (f : Syntax α → β → β) (b : β) : β :=
Id.run (s.mfoldSepArgs f b)

@[inline] def mforSepArgs (s : Syntax α) (f : Syntax α → m Unit) : m Unit :=
s.mfoldSepArgs (fun s _ => f s) ()

end

end Syntax
end Lean
