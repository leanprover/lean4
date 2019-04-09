import init.lean.name init.lean.position init.lean.parser.trie init.lean.parser.identifier
import syntax

open Lean
export Lean.Parser (Trie)
-- namespace Lean
namespace Parser

structure FrontendConfig :=
(filename : String)
(input    : String)
(fileMap  : FileMap)

structure TokenConfig :=
(val : String)
(lbp : Nat := 0)

namespace TokenConfig

def beq : TokenConfig → TokenConfig → Bool
| ⟨prefix₁, lbp₁⟩ ⟨prefix₂, lbp₂⟩ := prefix₁ == prefix₂ && lbp₁ == lbp₂

instance : HasBeq TokenConfig :=
⟨beq⟩

end TokenConfig

structure TokenCacheEntry :=
(startPos stopPos : String.Pos)
(token : Syntax)

structure ParserCache :=
(tokenCache : Option TokenCacheEntry := none)

structure ParserConfig extends FrontendConfig :=
(tokens : Trie TokenConfig)

def CommandParserConfig := List String -- TODO

structure ParserData :=
(stxStack : Array Syntax) (pos : String.Pos) (cache : ParserCache) (errorMsg : Option String)

@[inline] def ParserData.hasError (d : ParserData) : Bool :=
d.errorMsg != none

@[inline] def ParserData.stackSize (d : ParserData) : Nat :=
d.stxStack.size

def ParserData.restore (d : ParserData) (iniStackSz : Nat) (iniPos : Nat) : ParserData :=
match d with
| ⟨stack, _, cache, _⟩ := ⟨stack.shrink iniStackSz, iniPos, cache, none⟩

def ParserData.setPos (d : ParserData) (pos : Nat) : ParserData :=
match d with
| ⟨stack, _, cache, msg⟩ := ⟨stack, pos, cache, msg⟩

def ParserData.setCache (d : ParserData) (cache : ParserCache) : ParserData :=
match d with
| ⟨stack, pos, _, msg⟩ := ⟨stack, pos, cache, msg⟩

def ParserData.pushSyntax (d : ParserData) (n : Syntax) : ParserData :=
match d with
| ⟨stack, pos, cache, msg⟩ := ⟨stack.push n, pos, cache, msg⟩

def ParserData.next (d : ParserData) (s : String) (pos : Nat) : ParserData :=
d.setPos (s.next pos)

def ParserFn := String → ParserData → ParserData

instance : Inhabited ParserFn :=
⟨λ s, id⟩

structure ParserInfo :=
(updateTokens : NameSet → NameSet  := λ m, m)
(firstToken   : Option TokenConfig := none)

@[inline] def andthenFn (p q : ParserFn) : ParserFn
| s d :=
  let d := p s d in
  if d.hasError then d else q s d

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstToken   := p.firstToken }

def ParserData.mkNode (d : ParserData) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserData :=
match d with
| ⟨stack, pos, cache, err⟩ :=
  if err != none && stack.size == iniStackSz then
    -- If there is an error but there are no new nodes on the stack, we just return `d`
    d
  else
    let newNode := Syntax.node k (stack.extract iniStackSz stack.size) [] in
    let stack   := stack.shrink iniStackSz in
    let stack   := stack.push newNode in
    ⟨stack, pos, cache, err⟩

@[inline] def nodeFn (k : SyntaxNodeKind) (p : ParserFn) : ParserFn
| s d :=
  let iniSz := d.stackSize in
  let d     := p s d in
  d.mkNode k iniSz

@[noinline] def nodeInfo (p : ParserInfo) : ParserInfo :=
{ updateTokens := p.updateTokens,
  firstToken   := p.firstToken }

@[inline] def orelseFn (p q : ParserFn) : ParserFn
| s d :=
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  let d      := p s d in
  if d.hasError && d.pos == iniPos then q s (d.restore iniSz iniPos) else d

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstToken   :=
  match p.firstToken, q.firstToken with
  | some tk₁, some tk₂ := if tk₁ == tk₂ then some tk₁ else none
  | _, _               := none }

def ParserData.resetPos : ParserData → String.Pos → ParserData
| ⟨stack, _, cache, errorMsg⟩ pos := ⟨stack, pos, cache, errorMsg⟩

@[inline] def tryFn (p : ParserFn) : ParserFn
| s d :=
  let iniPos := d.pos in
  let d := p s d in
  if d.hasError then d.resetPos iniPos else d

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ updateTokens := info.updateTokens,
  firstToken   := none }

@[inline] def optionalFn (p : ParserFn) : ParserFn :=
λ s d,
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  let d := p s d in
  let d := if d.hasError then d.restore iniSz iniPos else d in
  d.mkNode nullKind iniSz

def ParserData.mkError (d : ParserData) (msg : String) : ParserData :=
match d with
| ⟨stack, pos, cache, _⟩ := ⟨stack, pos, cache, some msg⟩

def ParserData.mkEOIError (d : ParserData) : ParserData :=
d.mkError "end of input"

@[specialize] partial def manyAux (p : ParserFn) : String → ParserData → ParserData
| s d :=
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  let d      := p s d in
  if d.hasError then d.restore iniSz iniPos
  else if iniPos == d.pos then d.mkError "invalid 'many' parser combinator application, parser did not consume anything"
  else manyAux s d

@[inline] def manyFn (p : ParserFn) : ParserFn
| s d :=
  let iniSz  := d.stackSize in
  let d := manyAux p s d in
  d.mkNode nullKind iniSz

@[specialize] partial def satisfyFn (p : Char → Bool) (errorMsg : String := "unexpected character") : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    if p c then d.next s i
    else d.mkError errorMsg

@[specialize] partial def takeUntilFn (p : Char → Bool) : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d
  else
    let c := s.get i in
    if p c then d
    else takeUntilFn s (d.next s i)

@[specialize] def takeWhileFn (p : Char → Bool) : ParserFn :=
takeUntilFn (λ c, !p c)

@[inline] def takeWhile1Fn (p : Char → Bool) (errorMsg : String) : ParserFn :=
andthenFn (satisfyFn p errorMsg) (takeWhileFn p)

partial def finishCommentBlock : Nat → ParserFn
| nesting s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    let i := s.next i in
    if c == '-' then
      if s.atEnd i then d.mkEOIError
      else
        let c := s.get i in
        if c == '/' then -- "-/" end of comment
          if nesting == 1 then d.next s i
          else finishCommentBlock (nesting-1) s (d.next s i)
        else
          finishCommentBlock nesting s (d.next s i)
    else if c == '/' then
      if s.atEnd i then d.mkEOIError
      else
        let c := s.get i in
        if c == '-' then finishCommentBlock (nesting+1) s (d.next s i)
        else finishCommentBlock nesting s (d.setPos i)
    else finishCommentBlock nesting s (d.setPos i)

/- Consume whitespace and comments -/
partial def whitespace : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d
  else
    let c := s.get i in
    if c.isWhitespace then whitespace s (d.next s i)
    else if c == '-' then
      let i := s.next i in
      let c := s.get i in
      if c == '-' then andthenFn (takeUntilFn (= '\n')) whitespace s (d.next s i)
      else d
    else if c == '/' then
      let i := s.next i in
      let c := s.get i in
      if c == '-' then
        let i := s.next i in
        let c := s.get i in
        if c == '-' then d -- "/--" doc comment is an actual token
        else andthenFn (finishCommentBlock 1) whitespace s (d.next s i)
      else d
    else d

def mkEmptySubstringAt (s : String) (p : Nat) : Substring :=
{str := s, startPos := p, stopPos := p }

private def rawAux (startPos : Nat) (trailingWs : Bool) : ParserFn
| s d :=
  let stopPos := d.pos in
  let leading := mkEmptySubstringAt s startPos in
  let val     := s.extract startPos stopPos in
  if trailingWs then
    let d        := whitespace s d in
    let stopPos' := d.pos in
    let trailing : Substring := { str := s, startPos := stopPos, stopPos := stopPos' } in
    let atom := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val in
    d.pushSyntax atom
  else
    let trailing := mkEmptySubstringAt s stopPos in
    let atom := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val in
    d.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
@[inline] def rawFn (p : ParserFn) (trailingWs := false) : ParserFn
| s d :=
  let startPos := d.pos in
  let d := p s d in
  if d.hasError then d else rawAux startPos trailingWs s d

def hexDigitFn : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    let i := s.next i in
    if c.isDigit || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F') then d.setPos i
    else d.mkError "invalid hexadecimal numeral, hexadecimal digit expected"

def quotedCharFn : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    if c == '\\' || c == '\"' || c == '\'' || c == '\n' || c == '\t' then
      d.next s i
    else if c == 'x' then
      andthenFn hexDigitFn hexDigitFn s (d.next s i)
    else if c == 'u' then
      andthenFn hexDigitFn (andthenFn hexDigitFn (andthenFn hexDigitFn hexDigitFn)) s (d.next s i)
    else
      d.mkError "invalid escape sequence"

partial def strLitFnAux : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    let d := d.setPos (s.next i) in
    if c == '\"' then d
    else if c == '\\' then andthenFn quotedCharFn strLitFnAux s d
    else strLitFnAux s d

def strLitFn : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    if c == '\"' then strLitFnAux s (d.next s i)
    else d.mkError "expected string literal"

def decimalNumberFn : ParserFn
| s d :=
  let d := takeWhileFn (λ c, c.isDigit) s d in
  let i := d.pos in
  let c := s.get i in
  if c == '.' then
    let i := s.next i in
    let c := s.get i in
    if c.isDigit then
      takeWhileFn (λ c, c.isDigit) s (d.setPos i)
    else
      d
  else
    d

def binNumberFn : ParserFn :=
takeWhile1Fn (λ c, c == '0' || c == '1') "expected binary number"

def octalNumberFn : ParserFn :=
takeWhile1Fn (λ c, '0' ≤ c && c ≤ '7') "expected octal number"

def hexNumberFn : ParserFn :=
takeWhile1Fn (λ c, ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "expected hexadecimal number"

def numberFn : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    if c == '0' then
      let i := s.next i in
      let c := s.get i in
      if c == 'b' || c == 'B' then
        binNumberFn s (d.next s i)
      else if c == 'o' || c == 'O' then
        octalNumberFn s (d.next s i)
      else if c == 'x' || c == 'X' then
        hexNumberFn s (d.next s i)
      else
        decimalNumberFn s (d.next s i)
    else if c.isDigit then
      decimalNumberFn s (d.next s i)
    else
      d.mkError "expected numeral"

def isIdCont : String → ParserData → Bool
| s d :=
  let i := d.pos in
  let c := s.get i in
  if c == '.' then
    let i := s.next i in
    if s.atEnd i then
      false
    else
      let c := s.get i in
      isIdFirst c || isIdBeginEscape c
  else
    false

def mkIdResult (startPos : Nat) (val : Name) (s : String) (d : ParserData) : ParserData :=
let stopPos              := d.pos in
let rawVal : Substring   := { str := s, startPos := startPos, stopPos := stopPos } in
let d                    := whitespace s d in
let trailingStopPos      := d.pos in
let leading              := mkEmptySubstringAt s startPos in
let trailing : Substring := { str := s, startPos := stopPos, stopPos := trailingStopPos } in
let info : SourceInfo    := {leading := leading, trailing := trailing, pos := startPos} in
let atom                 := Syntax.ident (some info) rawVal val [] [] in
d.pushSyntax atom

partial def identFnAux (startPos : Nat) : Name → ParserFn
| r s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    if isIdBeginEscape c then
      let startPart := s.next i in
      let d := takeUntilFn isIdEndEscape s (d.setPos startPart) in
      let stopPart := d.pos in
      let d := satisfyFn isIdEndEscape "end of escaped identifier expected" s d in
      if d.hasError then d
      else
        let r := Name.mkString r (s.extract startPart stopPart) in
        if isIdCont s d then
          identFnAux r s d
        else
          mkIdResult startPos r s d
    else if isIdFirst c then
      let startPart := i in
      let d := takeWhileFn isIdRest s (d.next s i) in
      let stopPart := d.pos in
      let r := Name.mkString r (s.extract startPart stopPart) in
      if isIdCont s d then
        identFnAux r s d
      else
        mkIdResult startPart r s d
    else
      d.mkError "identifier expected"

@[inline] def identFn : ParserFn
| s d :=  identFnAux d.pos Name.anonymous s d

structure AbsParser (ρ : Type) :=
(info : Thunk ParserInfo) (fn : ρ)

abbrev Parser := AbsParser ParserFn

class ParserFnLift (ρ : Type) :=
(lift {} : ParserFn → ρ)
(map     : (ParserFn → ParserFn) → ρ → ρ)
(map₂    : (ParserFn → ParserFn → ParserFn) → ρ → ρ → ρ)

instance parserLiftInhabited {ρ : Type} [ParserFnLift ρ] : Inhabited ρ :=
⟨ParserFnLift.lift (default _)⟩

instance idParserLift : ParserFnLift ParserFn :=
{ lift := λ p, p,
  map  := λ m p, m p,
  map₂ := λ m p1 p2, m p1 p2 }

@[inline]
def liftParser {ρ : Type} [ParserFnLift ρ] (info : Thunk ParserInfo) (fn : ParserFn) : AbsParser ρ :=
{ info := info, fn := ParserFnLift.lift fn }

@[inline]
def mapParser {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn) : AbsParser ρ → AbsParser ρ :=
λ p, { info := Thunk.mk (λ _, infoFn p.info.get), fn := ParserFnLift.map pFn p.fn }

@[inline]
def mapParser₂ {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn → ParserFn)
               : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
λ p q, { info := Thunk.mk (λ _, infoFn p.info.get q.info.get), fn := ParserFnLift.map₂ pFn p.fn q.fn }

def EnvParserFn (α : Type) (ρ : Type) :=
α → ρ

def RecParserFn (α ρ : Type) :=
EnvParserFn (α → ρ) ρ

instance envParserLift (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (EnvParserFn α ρ) :=
{ lift    := λ p a, ParserFnLift.lift p,
  map     := λ m p a, ParserFnLift.map m (p a),
  map₂    := λ m p1 p2 a, ParserFnLift.map₂ m (p1 a) (p2 a) }

instance recParserLift (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (RecParserFn α ρ) :=
inferInstanceAs (ParserFnLift (EnvParserFn (α → ρ) ρ))

namespace RecParserFn
variables {α ρ : Type}

@[inline] def recurse (a : α) : RecParserFn α ρ :=
λ p, p a

@[inline] def run [ParserFnLift ρ] (x : RecParserFn α ρ) (rec : α → RecParserFn α ρ) : ρ :=
x (fix (λ f a, rec a f))

end RecParserFn

@[inline] def andthen {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ andthenInfo andthenFn

@[inline] def node {ρ : Type} [ParserFnLift ρ] (k : SyntaxNodeKind) : AbsParser ρ → AbsParser ρ :=
mapParser nodeInfo (nodeFn k)

@[inline] def orelse {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ orelseInfo orelseFn

@[inline] def try {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo tryFn

@[inline] def many {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo manyFn

@[inline] def optional {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo optionalFn

@[inline] def many1 {ρ : Type} [ParserFnLift ρ] (p : AbsParser ρ) : AbsParser ρ :=
andthen p (many p)

abbrev BasicParserFn : Type          := EnvParserFn ParserConfig ParserFn
abbrev BasicParser : Type            := AbsParser BasicParserFn
abbrev CmdParserFn (ρ : Type) : Type := EnvParserFn ρ (RecParserFn Unit ParserFn)
abbrev TermParserFn : Type           := RecParserFn Nat (CmdParserFn ParserConfig)
abbrev TermParser : Type             := AbsParser TermParserFn
abbrev TrailingTermParser : Type     := AbsParser (EnvParserFn Syntax TermParserFn)
abbrev CommandParser : Type          := AbsParser (CmdParserFn CommandParserConfig)

@[inline] def Term.parser (rbp : Nat := 0) : TermParser :=
{ info := Thunk.pure {}, fn := RecParserFn.recurse rbp }

@[inline] def Command.parser : CommandParser :=
{ info := Thunk.pure {}, fn := λ _, RecParserFn.recurse () }

@[inline] def basicParser2TermParser (p : BasicParser) : TermParser :=
{ info := Thunk.mk (λ _, p.info.get), fn := λ _ cfg _, p.fn cfg }

instance basic2term : HasCoe BasicParser TermParser :=
⟨basicParser2TermParser⟩

private def tokenFnAux : BasicParserFn
| cfg s d := d -- TODO

def tokenFn : BasicParserFn
| cfg s d :=
  let i := d.pos in
  match d.cache with
  | { tokenCache := some tkc } :=
    if tkc.startPos == i then
      let d := d.pushSyntax tkc.token in
      d.setPos tkc.stopPos
    else tokenFnAux cfg s d
  | _ :=  tokenFnAux cfg s d

#exit

local infix ` ; `:10 := Parser.andthen
local infix ` || `:5 := Parser.orelse

def mkTestKind : IO SyntaxNodeKind := nextKind `test
@[init mkTestKind] constant testKind : SyntaxNodeKind := default _

set_option pp.implicit true
set_option pp.binder_types false
set_option trace.compiler.stage2 true
-- set_option trace.compiler.boxed true
-- set_option trace.compiler.stage1 true
-- set_option trace.compiler.lcnf true
-- set_option trace.compiler.lcnf true
-- set_option trace.compiler.simp true

@[inline2]
def p0 : BasicParser :=
node testKind (token "foo"; many (token "boo"))

@[inline2]
def p1 (s : String) : TermParser :=
token "hello"; token "world"; token "boo"
||
token s
||
token "opt3"; token "boo"

@[inline2]
def p2 (s : String) : TermParser :=
-- token "boo"; p1; p1; p0
p1 "hello"; p0; p1 s

@[inline2]
def p3 (s : String) : TermParser :=
p1 s
||
p2 s
||
token "boo"; p2 s

@[inline2]
def p4 (s : String) : CommandParser :=
token s; token "boo"

end Parser
-- end Lean
