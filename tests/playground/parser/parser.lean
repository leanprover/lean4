import init.lean.name init.lean.parser.trie init.lean.parser.identifier
import syntax filemap

open Lean
export Lean.Parser (Trie)
-- namespace Lean
namespace Parser

/-- A multimap indexed by tokens. Used for indexing parsers by their leading token. -/
def TokenMap (α : Type) := RBMap Name (List α) Name.quickLt

namespace TokenMap

def insert {α : Type} (map : TokenMap α) (k : Name) (v : α) : TokenMap α :=
match map.find k with
| none    := map.insert k [v]
| some vs := map.insert k (v::vs)

def ofListAux {α : Type} : List (Name × α) → TokenMap α → TokenMap α
| []          m := m
| (⟨k,v⟩::xs) m := ofListAux xs (m.insert k v)

def ofList {α : Type} (es : List (Name × α)) : TokenMap α :=
ofListAux es RBMap.empty

end TokenMap

structure FrontendConfig :=
(filename : String)
(input    : String)
(fileMap  : FileMap)

structure TokenConfig :=
(val : String)
(lbp : Nat := 0)

namespace TokenConfig

def beq : TokenConfig → TokenConfig → Bool
| ⟨val₁, lbp₁⟩ ⟨val₂, lbp₂⟩ := val₁ == val₂ && lbp₁ == lbp₂

instance : BEq TokenConfig :=
⟨beq⟩

end TokenConfig

structure TokenCacheEntry :=
(startPos stopPos : String.Pos)
(token : Syntax)

structure ParserCache :=
(tokenCache : Option TokenCacheEntry := none)

structure ParserConfig extends FrontendConfig :=
(tokens : Trie TokenConfig)

structure ParserData :=
(stxStack : Array Syntax) (pos : String.Pos) (cache : ParserCache) (errorMsg : Option String)

@[inline] def ParserData.hasError (d : ParserData) : Bool :=
d.errorMsg != none

@[inline] def ParserData.stackSize (d : ParserData) : Nat :=
d.stxStack.size

def ParserData.restore (d : ParserData) (iniStackSz : Nat) (iniPos : Nat) : ParserData :=
{ stxStack := d.stxStack.take iniStackSz, errorMsg := none, pos := iniPos, .. d}

def ParserData.setPos (d : ParserData) (pos : Nat) : ParserData :=
{ pos := pos, .. d }

def ParserData.setCache (d : ParserData) (cache : ParserCache) : ParserData :=
{ cache := cache, .. d }

def ParserData.pushSyntax (d : ParserData) (n : Syntax) : ParserData :=
{ stxStack := d.stxStack.push n, .. d }

def ParserData.takeStack (d : ParserData) (iniStackSz : Nat) : ParserData :=
{ stxStack := d.stxStack.take iniStackSz, .. d }

def ParserData.next (d : ParserData) (s : String) (pos : Nat) : ParserData :=
{ pos := s.next pos, .. d }

def ParserData.toErrorMsg (d : ParserData) (cfg : ParserConfig) : String :=
match d.errorMsg with
| none     := ""
| some msg :=
  let pos := cfg.fileMap.toPosition d.pos in
  cfg.filename ++ ":" ++ toString pos.line ++ ":" ++ toString pos.column ++ " " ++ msg

def ParserFn := String → ParserData → ParserData

instance : Inhabited ParserFn :=
⟨λ s, id⟩

structure ParserInfo :=
(updateTokens : Trie TokenConfig → Trie TokenConfig := λ tks, tks)
(firstTokens  : List TokenConfig := [])

@[inline] def andthenFn (p q : ParserFn) : ParserFn
| s d :=
  let d := p s d in
  if d.hasError then d else q s d

@[noinline] def andthenInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstTokens  := p.firstTokens }

def ParserData.mkNode (d : ParserData) (k : SyntaxNodeKind) (iniStackSz : Nat) : ParserData :=
match d with
| ⟨stack, pos, cache, err⟩ :=
  if err != none && stack.size == iniStackSz then
    -- If there is an error but there are no new nodes on the stack, we just return `d`
    d
  else
    let newNode := Syntax.node k (stack.extract iniStackSz stack.size) [] in
    let stack   := stack.take iniStackSz in
    let stack   := stack.push newNode in
    ⟨stack, pos, cache, err⟩

@[inline] def nodeFn (k : SyntaxNodeKind) (p : ParserFn) : ParserFn
| s d :=
  let iniSz := d.stackSize in
  let d     := p s d in
  d.mkNode k iniSz

@[noinline] def nodeInfo (p : ParserInfo) : ParserInfo :=
{ updateTokens := p.updateTokens,
  firstTokens  := p.firstTokens }

@[inline] def orelseFn (p q : ParserFn) : ParserFn
| s d :=
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  let d      := p s d in
  if d.hasError && d.pos == iniPos then q s (d.restore iniSz iniPos) else d

@[noinline] def orelseInfo (p q : ParserInfo) : ParserInfo :=
{ updateTokens := q.updateTokens ∘ p.updateTokens,
  firstTokens  := p.firstTokens ++ q.firstTokens }

@[inline] def tryFn (p : ParserFn) : ParserFn
| s d :=
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  match p s d with
  | ⟨stack, _, cache, some msg⟩ := ⟨stack.take iniSz, iniPos, cache, some msg⟩
  | other                       := other

@[noinline] def noFirstTokenInfo (info : ParserInfo) : ParserInfo :=
{ updateTokens := info.updateTokens,
  firstTokens  := [] }

@[inline] def optionalFn (p : ParserFn) : ParserFn :=
λ s d,
  let iniSz  := d.stackSize in
  let iniPos := d.pos in
  let d      := p s d in
  let d      := if d.hasError then d.restore iniSz iniPos else d in
  d.mkNode nullKind iniSz

def ParserData.mkError (d : ParserData) (msg : String) : ParserData :=
match d with
| ⟨stack, pos, cache, _⟩ := ⟨stack, pos, cache, some msg⟩

def ParserData.mkEOIError (d : ParserData) : ParserData :=
d.mkError "end of input"

def ParserData.mkErrorAt (d : ParserData) (msg : String) (pos : String.Pos) : ParserData :=
match d with
| ⟨stack, _, cache, _⟩ := ⟨stack, pos, cache, some msg⟩

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

@[specialize] private partial def sepByFnAux (p : ParserFn) (sep : ParserFn) (allowTrailingSep : Bool) (iniSz : Nat) : Bool → ParserFn
| pOpt s d :=
  let sz  := d.stackSize in
  let pos := d.pos in
  let d   := p s d in
  if d.hasError then
    let d := d.restore sz pos in
    if pOpt then
      d.mkNode nullKind iniSz
    else
      -- append `Syntax.missing` to make clear that List is incomplete
      let d := d.pushSyntax Syntax.missing in
      d.mkNode nullKind iniSz
  else
    let sz  := d.stackSize in
    let pos := d.pos in
    let d   := sep s d in
    if d.hasError then
      let d := d.restore sz pos in
      d.mkNode nullKind iniSz
    else
      sepByFnAux allowTrailingSep s d

@[specialize] def sepByFn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn
| s d :=
  let iniSz := d.stackSize in
  sepByFnAux p sep allowTrailingSep iniSz true s d

@[specialize] def sepBy1Fn (allowTrailingSep : Bool) (p : ParserFn) (sep : ParserFn) : ParserFn
| s d :=
  let iniSz := d.stackSize in
  sepByFnAux p sep allowTrailingSep iniSz false s d

@[noinline] def sepByInfo (p sep : ParserInfo) : ParserInfo :=
{ updateTokens := sep.updateTokens ∘ p.updateTokens,
  firstTokens  := [] }

@[noinline] def sepBy1Info (p sep : ParserInfo) : ParserInfo :=
{ updateTokens := sep.updateTokens ∘ p.updateTokens,
  firstTokens  := p.firstTokens }

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

def mkStrLitKind : IO SyntaxNodeKind := nextKind `strLit
@[init mkStrLitKind] constant strLitKind : SyntaxNodeKind := default _

/-- Push `(Syntax.node tk <new-atom>)` into syntax stack -/
def mkNodeToken (k : SyntaxNodeKind) (startPos : Nat) (s : String) (d : ParserData) : ParserData :=
let stopPos   := d.pos in
let leading   := mkEmptySubstringAt s startPos in
let val       := s.extract startPos stopPos in
let d         := whitespace s d in
let wsStopPos := d.pos in
let trailing  := { Substring . str := s, startPos := stopPos, stopPos := wsStopPos } in
let atom      := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val in
let tk        := Syntax.node k (Array.singleton atom) [] in
d.pushSyntax tk

partial def strLitFnAux (startPos : Nat) : ParserFn
| s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    let c := s.get i in
    let d := d.setPos (s.next i) in
    if c == '\"' then
      mkNodeToken strLitKind startPos s d
    else if c == '\\' then andthenFn quotedCharFn strLitFnAux s d
    else strLitFnAux s d

def mkNumberKind : IO SyntaxNodeKind := nextKind `number
@[init mkNumberKind] constant numberKind : SyntaxNodeKind := default _

def decimalNumberFn (startPos : Nat) : ParserFn
| s d :=
  let d := takeWhileFn (λ c, c.isDigit) s d in
  let i := d.pos in
  let c := s.get i in
  let d :=
    if c == '.' then
      let i := s.next i in
      let c := s.get i in
      if c.isDigit then
        takeWhileFn (λ c, c.isDigit) s (d.setPos i)
      else
        d
    else
      d in
  mkNodeToken numberKind startPos s d

def binNumberFn (startPos : Nat) : ParserFn
| s d :=
  let d := takeWhile1Fn (λ c, c == '0' || c == '1') "expected binary number" s d in
  mkNodeToken numberKind startPos s d

def octalNumberFn (startPos : Nat) : ParserFn
| s d :=
  let d := takeWhile1Fn (λ c, '0' ≤ c && c ≤ '7') "expected octal number" s d in
  mkNodeToken numberKind startPos s d

def hexNumberFn (startPos : Nat) : ParserFn
| s d :=
  let d := takeWhile1Fn (λ c, ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')) "expected hexadecimal number" s d in
  mkNodeToken numberKind startPos s d

def numberFnAux : ParserFn
| s d :=
  let startPos := d.pos in
  if s.atEnd startPos then d.mkEOIError
  else
    let c := s.get startPos in
    if c == '0' then
      let i := s.next startPos in
      let c := s.get i in
      if c == 'b' || c == 'B' then
        binNumberFn startPos s (d.next s i)
      else if c == 'o' || c == 'O' then
        octalNumberFn startPos s (d.next s i)
      else if c == 'x' || c == 'X' then
        hexNumberFn startPos s (d.next s i)
      else
        decimalNumberFn startPos s (d.setPos i)
    else if c.isDigit then
      decimalNumberFn startPos s (d.next s startPos)
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

private def isToken (idStartPos idStopPos : Nat) (tk : Option TokenConfig) : Bool :=
match tk with
| none    := false
| some tk :=
   -- if a token is both a symbol and a valid identifier (i.e. a keyword),
   -- we want it to be recognized as a symbol
  tk.val.bsize ≥ idStopPos - idStopPos


def mkTokenAndFixPos (startPos : Nat) (tk : Option TokenConfig) (s : String) (d : ParserData) : ParserData :=
match tk with
| none    := d.mkErrorAt "token expected" startPos
| some tk :=
  let leading   := mkEmptySubstringAt s startPos in
  let val       := tk.val in
  let stopPos   := startPos + val.bsize in
  let d         := d.setPos stopPos in
  let d         := whitespace s d in
  let wsStopPos := d.pos in
  let trailing  := { Substring . str := s, startPos := stopPos, stopPos := wsStopPos } in
  let atom      := Syntax.atom (some { leading := leading, pos := startPos, trailing := trailing }) val in
  d.pushSyntax atom

def mkIdResult (startPos : Nat) (tk : Option TokenConfig) (val : Name) (s : String) (d : ParserData) : ParserData :=
let stopPos              := d.pos in
if isToken startPos stopPos tk then
  mkTokenAndFixPos startPos tk s d
else
  let rawVal : Substring   := { str := s, startPos := startPos, stopPos := stopPos } in
  let d                    := whitespace s d in
  let trailingStopPos      := d.pos in
  let leading              := mkEmptySubstringAt s startPos in
  let trailing : Substring := { str := s, startPos := stopPos, stopPos := trailingStopPos } in
  let info : SourceInfo    := {leading := leading, trailing := trailing, pos := startPos} in
  let atom                 := Syntax.ident (some info) rawVal val [] [] in
  d.pushSyntax atom

partial def identFnAux (startPos : Nat) (tk : Option TokenConfig) : Name → ParserFn
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
          mkIdResult startPos tk r s d
    else if isIdFirst c then
      let startPart := i in
      let d := takeWhileFn isIdRest s (d.next s i) in
      let stopPart := d.pos in
      let r := Name.mkString r (s.extract startPart stopPart) in
      if isIdCont s d then
        identFnAux r s d
      else
        mkIdResult startPart tk r s d
    else
      mkTokenAndFixPos startPos tk s d

def ParserData.keepNewError (d : ParserData) (oldStackSize : Nat) : ParserData :=
match d with
| ⟨stack, pos, cache, err⟩ := ⟨stack.take oldStackSize, pos, cache, err⟩

def ParserData.keepPrevError (d : ParserData) (oldStackSize : Nat) (oldStopPos : String.Pos) (oldError : Option String) : ParserData :=
match d with
| ⟨stack, _, cache, _⟩ := ⟨stack.take oldStackSize, oldStopPos, cache, oldError⟩

def ParserData.mergeErrors (d : ParserData) (oldStackSize : Nat) (oldError : String) : ParserData :=
match d with
| ⟨stack, pos, cache, some err⟩ := ⟨stack.take oldStackSize, pos, cache, some (err ++ "; " ++ oldError)⟩
| other                         := other

def ParserData.mkLongestNodeAlt (d : ParserData) (startSize : Nat) : ParserData :=
match d with
| ⟨stack, pos, cache, _⟩ :=
  if stack.size == startSize then ⟨stack.push Syntax.missing, pos, cache, none⟩ -- parser did not create any node, then we just add `Syntax.missing`
  else if stack.size == startSize + 1 then d
  else
    -- parser created more than one node, combine them into a single node
    let node := Syntax.node nullKind (stack.extract startSize stack.size) [] in
    let stack := stack.take startSize in
    ⟨stack.push node, pos, cache, none⟩

def ParserData.keepLatest (d : ParserData) (startStackSize : Nat) : ParserData :=
match d with
| ⟨stack, pos, cache, _⟩ :=
  let node  := stack.back in
  let stack := stack.take startStackSize in
  let stack := stack.push node in
  ⟨stack, pos, cache, none⟩

def ParserData.replaceLongest (d : ParserData) (startStackSize : Nat) (prevStackSize : Nat) : ParserData :=
let d := d.mkLongestNodeAlt prevStackSize in
d.keepLatest startStackSize

def longestMatchStep (startSize : Nat) (startPos : String.Pos) (p : ParserFn) : ParserFn :=
λ s d,
let prevErrorMsg  := d.errorMsg in
let prevStopPos   := d.pos in
let prevSize      := d.stackSize in
let d             := d.restore prevSize startPos in
let d             := p s d in
match prevErrorMsg, d.errorMsg with
| none, none   := -- both succeeded
  if d.pos > prevStopPos      then d.replaceLongest startSize prevSize -- replace
  else if d.pos < prevStopPos then d.restore prevSize prevStopPos      -- keep prev
  else d.mkLongestNodeAlt prevSize                                     -- keep both
| none, some _ := -- prev succeeded, current failed
  d.restore prevSize prevStopPos
| some oldError, some _ := -- both failed
  if d.pos > prevStopPos      then d.keepNewError prevSize
  else if d.pos < prevStopPos then d.keepPrevError prevSize prevStopPos prevErrorMsg
  else d.mergeErrors prevSize oldError
| some _, none := -- prev failed, current succeeded
  d.mkLongestNodeAlt startSize

def longestMatchMkResult (startSize : Nat) (d : ParserData) : ParserData :=
if !d.hasError && d.stackSize > startSize + 1 then d.mkNode choiceKind startSize else d

def longestMatchFnAux (startSize : Nat) (startPos : String.Pos) : List ParserFn → ParserFn
| []      := λ _ d, longestMatchMkResult startSize d
| (p::ps) := λ s d,
   let d := longestMatchStep startSize startPos p s d in
   longestMatchFnAux ps s d

def longestMatchFn₁ (p : ParserFn) : ParserFn :=
λ s d,
let startSize := d.stackSize in
let d := p s d in
if d.hasError then d else d.mkLongestNodeAlt startSize

def longestMatchFn₂ (p q : ParserFn) : ParserFn :=
λ s d,
let startSize := d.stackSize in
let startPos  := d.pos in
let d         := p s d in
let d         := if d.hasError then d.takeStack startSize else d.mkLongestNodeAlt startSize in
let d         := longestMatchStep startSize startPos q s d in
longestMatchMkResult startSize d

def longestMatchFn : List ParserFn → ParserFn
| []      := λ _ d, d.mkError "longest match: empty list"
| [p]     := longestMatchFn₁ p
| (p::ps) := λ s d,
  let startSize := d.stackSize in
  let startPos  := d.pos in
  let d         := p s d in
  if d.hasError then
    let d := d.takeStack startSize in
    longestMatchFnAux startSize startPos ps s d
  else
    let d := d.mkLongestNodeAlt startSize in
    longestMatchFnAux startSize startPos ps s d

structure AbsParser (ρ : Type) :=
(info : ParserInfo := {})
(fn   : ρ)

abbrev Parser := AbsParser ParserFn

class ParserFnLift (ρ : Type) :=
(lift {} : ParserFn → ρ)
(map     : (ParserFn → ParserFn) → ρ → ρ)
(map₂    : (ParserFn → ParserFn → ParserFn) → ρ → ρ → ρ)
(mapList : (List ParserFn → ParserFn) → List ρ → ρ)

instance parserLiftInhabited {ρ : Type} [ParserFnLift ρ] : Inhabited ρ :=
⟨ParserFnLift.lift (default _)⟩

instance idParserLift : ParserFnLift ParserFn :=
{ lift    := λ p, p,
  map     := λ m p, m p,
  map₂    := λ m p1 p2, m p1 p2,
  mapList := λ m ps, m ps }

@[inline]
def liftParser {ρ : Type} [ParserFnLift ρ] (info : ParserInfo) (fn : ParserFn) : AbsParser ρ :=
{ info := info, fn := ParserFnLift.lift fn }

@[inline]
def mapParser {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn) : AbsParser ρ → AbsParser ρ :=
λ p, { info := infoFn p.info, fn := ParserFnLift.map pFn p.fn }

@[inline]
def mapParser₂ {ρ : Type} [ParserFnLift ρ] (infoFn : ParserInfo → ParserInfo → ParserInfo) (pFn : ParserFn → ParserFn → ParserFn)
               : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
λ p q, { info := infoFn p.info q.info, fn := ParserFnLift.map₂ pFn p.fn q.fn }

def EnvParserFn (α : Type) (ρ : Type) :=
α → ρ

def RecParserFn (α ρ : Type) :=
EnvParserFn (α → ρ) ρ

instance envParserLift (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (EnvParserFn α ρ) :=
{ lift    := λ p a, ParserFnLift.lift p,
  map     := λ m p a, ParserFnLift.map m (p a),
  map₂    := λ m p1 p2 a, ParserFnLift.map₂ m (p1 a) (p2 a),
  mapList := λ m ps a, ParserFnLift.mapList m (ps.map (λ p, p a)) }

instance recParserLift (α ρ : Type) [ParserFnLift ρ] : ParserFnLift (RecParserFn α ρ) :=
inferInstanceAs (ParserFnLift (EnvParserFn (α → ρ) ρ))

namespace RecParserFn
variable {α ρ : Type}

@[inline] def recurse (a : α) : RecParserFn α ρ :=
λ p, p a

@[inline] def run [ParserFnLift ρ] (x : RecParserFn α ρ) (rec : α → RecParserFn α ρ) : ρ :=
x (fix (λ f a, rec a f))

end RecParserFn

@[inline] def andthen {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ andthenInfo andthenFn

instance absParserAndThen {ρ : Type} [ParserFnLift ρ] : AndThen (AbsParser ρ) :=
⟨andthen⟩

@[inline] def node {ρ : Type} [ParserFnLift ρ] (k : SyntaxNodeKind) : AbsParser ρ → AbsParser ρ :=
mapParser nodeInfo (nodeFn k)

@[inline] def orelse {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ → AbsParser ρ :=
mapParser₂ orelseInfo orelseFn

instance absParserOrElse {ρ : Type} [ParserFnLift ρ] : OrElse (AbsParser ρ) :=
⟨orelse⟩

@[inline] def try {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo tryFn

@[inline] def many {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo manyFn

@[inline] def optional {ρ : Type} [ParserFnLift ρ] : AbsParser ρ → AbsParser ρ :=
mapParser noFirstTokenInfo optionalFn

@[inline] def many1 {ρ : Type} [ParserFnLift ρ] (p : AbsParser ρ) : AbsParser ρ :=
andthen p (many p)

@[inline] def sepBy {ρ : Type} [ParserFnLift ρ] (p sep : AbsParser ρ) (allowTrailingSep : Bool := false) : AbsParser ρ :=
mapParser₂ sepByInfo (sepByFn allowTrailingSep) p sep

@[inline] def sepBy1 {ρ : Type} [ParserFnLift ρ] (p sep : AbsParser ρ) (allowTrailingSep : Bool := false) : AbsParser ρ :=
mapParser₂ sepBy1Info (sepBy1Fn allowTrailingSep) p sep

def longestMatchInfo {ρ : Type} (ps : List (AbsParser ρ)) : ParserInfo :=
{ updateTokens := λ trie, ps.foldl (λ trie p, p.info.updateTokens trie) trie,
  firstTokens  := ps.foldl (λ tks p, p.info.firstTokens ++ tks) [] }

def liftLongestMatchFn {ρ : Type} [ParserFnLift ρ] : List (AbsParser ρ) → ρ
| []     := ParserFnLift.lift (longestMatchFn [])
| [p]    := ParserFnLift.map  longestMatchFn₁ p.fn
| [p, q] := ParserFnLift.map₂ longestMatchFn₂ p.fn q.fn
| ps     := ParserFnLift.mapList longestMatchFn (ps.map (λ p, p.fn))

@[inline] def longestMatch {ρ : Type} [ParserFnLift ρ] (ps : List (AbsParser ρ)) : AbsParser ρ :=
{ info := longestMatchInfo ps,
  fn   := liftLongestMatchFn ps }

abbrev BasicParserFn : Type          := EnvParserFn ParserConfig ParserFn
abbrev BasicParser : Type            := AbsParser BasicParserFn
abbrev CmdParserFn (ρ : Type) : Type := EnvParserFn ρ (RecParserFn Unit ParserFn)
abbrev TermParserFn : Type           := RecParserFn Nat (CmdParserFn ParserConfig)
abbrev TermParser : Type             := AbsParser TermParserFn
abbrev TrailingTermParserFn : Type   := EnvParserFn Syntax TermParserFn
abbrev TrailingTermParser : Type     := AbsParser TrailingTermParserFn

structure TermParsingTables :=
(leadingTermParsers       : TokenMap TermParserFn)
(trailingTermParsers      : TokenMap TrailingTermParserFn)
-- local Term parsers (such as from `local notation`) hide previous parsers instead of overloading them
(localLeadingTermParsers  : TokenMap TermParserFn         := RBMap.empty)
(localTrailingTermParsers : TokenMap TrailingTermParserFn := RBMap.empty)

structure CommandParserConfig extends ParserConfig :=
(pTables : TermParsingTables)

abbrev CommandParserFn : Type        := CmdParserFn CommandParserConfig
abbrev CommandParser : Type          := AbsParser CommandParserFn

@[inline] def Term.parser (rbp : Nat := 0) : TermParser :=
{ fn := RecParserFn.recurse rbp }

@[inline] def Command.parser : CommandParser :=
{ fn := λ _, RecParserFn.recurse () }

@[inline] def basicParser2TermParser (p : BasicParser) : TermParser :=
{ info := p.info, fn := λ _ cfg _, p.fn cfg }

instance basic2term : HasCoe BasicParser TermParser :=
⟨basicParser2TermParser⟩

@[inline] def basicParser2CmdParser (p : BasicParser) : CommandParser :=
{ info := p.info, fn := λ cfg _, p.fn cfg.toParserConfig }

instance basicmd : HasCoe BasicParser CommandParser :=
⟨basicParser2CmdParser⟩

private def tokenFnAux : BasicParserFn
| cfg s d :=
  let i := d.pos in
  let c := s.get i in
  if c == '\"' then
    strLitFnAux i s (d.next s i)
  else if c.isDigit then
    numberFnAux s d
  else
    let tk := cfg.tokens.matchPrefix s i in
    identFnAux i tk Name.anonymous s d

private def updateCache (startPos : Nat) (d : ParserData) : ParserData :=
match d with
| ⟨stack, pos, cache, none⟩ :=
  if stack.size == 0 then d
  else
    let tk := stack.back in
    ⟨stack, pos, { tokenCache := some { startPos := startPos, stopPos := pos, token := tk } }, none⟩
| other := other

def tokenFn : BasicParserFn
| cfg s d :=
  let i := d.pos in
  if s.atEnd i then d.mkEOIError
  else
    match d.cache with
    | { tokenCache := some tkc } :=
      if tkc.startPos == i then
        let d := d.pushSyntax tkc.token in
        d.setPos tkc.stopPos
      else
        let d := tokenFnAux cfg s d in
        updateCache i d
    | _ :=
      let d := tokenFnAux cfg s d in
      updateCache i d

@[inline] def satisfySymbolFn (p : String → Bool) (errorMsg : String) : BasicParserFn
| cfg s d :=
  let startPos := d.pos in
  let d        := tokenFn cfg s d in
  if d.hasError then
    d.mkErrorAt errorMsg startPos
  else
    match d.stxStack.back with
    | Syntax.atom _ sym := if p sym then d else d.mkErrorAt errorMsg startPos
    | _                 := d.mkErrorAt errorMsg startPos

def symbolFnAux (sym : String) (errorMsg : String) : BasicParserFn :=
satisfySymbolFn (== sym) errorMsg

@[inline] def symbolFn (sym : String) : BasicParserFn :=
symbolFnAux sym ("expected '" ++ sym ++ "'")

def symbolInfo (sym : String) (lbp : Nat) : ParserInfo :=
{ updateTokens := λ trie, trie.insert sym { val := sym, lbp := lbp },
  firstTokens  := [ { val := sym, lbp := lbp } ] }

@[inline] def symbol (sym : String) (lbp : Nat := 0) : BasicParser :=
{ info := symbolInfo sym lbp,
  fn   := symbolFn sym }

def unicodeSymbolFnAux (sym asciiSym : String) (errorMsg : String) : BasicParserFn :=
satisfySymbolFn (λ s, s == sym || s == asciiSym) errorMsg

@[inline] def unicodeSymbolFn (sym asciiSym : String) : BasicParserFn :=
unicodeSymbolFnAux sym asciiSym ("expected '" ++ sym ++ "' or '" ++ asciiSym ++ "'")

def unicodeSymbolInfo (sym asciiSym : String) (lbp : Nat) : ParserInfo :=
{ updateTokens := λ trie,
  let trie := trie.insert sym { val := sym, lbp := lbp } in
  trie.insert sym { val := asciiSym, lbp := lbp },
  firstTokens  := [ { val := sym, lbp := lbp },
                    { val := asciiSym, lbp := lbp } ] }

@[inline] def unicodeSymbol (sym asciiSym : String) (lbp : Nat := 0) : BasicParser :=
{ info := unicodeSymbolInfo sym asciiSym lbp,
  fn   := unicodeSymbolFn sym asciiSym }

def numberFn : BasicParserFn
| cfg s d :=
  let d := tokenFn cfg s d in
  if d.hasError || !(d.stxStack.back.isOfKind numberKind) then
    d.mkError "expected numeral"
  else
    d

@[inline] def number : BasicParser :=
{ fn := numberFn }

def strLitFn : BasicParserFn
| cfg s d :=
  let d := tokenFn cfg s d in
  if d.hasError || !(d.stxStack.back.isOfKind strLitKind) then
    d.mkError "expected string literal"
  else
    d

@[inline] def strLit : BasicParser :=
{ fn := numberFn }

def identFn : BasicParserFn
| cfg s d :=
  let d := tokenFn cfg s d in
  if d.hasError || !(d.stxStack.back.isIdent) then
    d.mkError "expected identifier"
  else
    d

@[inline] def ident : BasicParser :=
{ fn := identFn }

instance string2basic : HasCoe String BasicParser :=
⟨symbol⟩

def mkFrontendConfig (filename input : String) : FrontendConfig :=
{ filename := filename,
  input    := input,
  fileMap  := input.toFileMap }

def BasicParser.run (p : BasicParser) (input : String) (filename : String := "<input>") : Except String Syntax :=
let frontendCfg        := mkFrontendConfig filename input in
let tokens             := p.info.updateTokens {} in
let cfg : ParserConfig := { tokens := tokens, .. frontendCfg } in
let d : ParserData     := { stxStack := Array.empty, pos := 0, cache := {}, errorMsg := none } in
let d                  := p.fn cfg input d in
if d.hasError then
  Except.error (d.toErrorMsg cfg)
else
  Except.ok d.stxStack.back

-- Helper function for testing (non-recursive) term parsers
def TermParser.test (p : TermParser) (input : String) (filename : String := "<input>") : Except String Syntax :=
let frontendCfg        := mkFrontendConfig filename input in
let tokens             := p.info.updateTokens {} in
let cfg : ParserConfig := { tokens := tokens, .. frontendCfg } in
let d : ParserData     := { stxStack := Array.empty, pos := 0, cache := {}, errorMsg := none } in
let dummyCmdParser  : Unit → ParserFn := λ _ _ d, d.mkError "no command parser" in
let dummyTermParser : ℕ → CmdParserFn ParserConfig := λ _ _ _ _ d, d.mkError "no term parser" in
let d := p.fn dummyTermParser cfg dummyCmdParser input d in
if d.hasError then
  Except.error (d.toErrorMsg cfg)
else
  Except.ok d.stxStack.back

-- Stopped here

@[noinline] def termPrattParser (tbl : TermParsingTables) (rbp : Nat) : TermParserFn :=
λ g, g 0 -- TODO(Leo)

@[specialize] def TermParserFn.run (p : TermParserFn) : CommandParserFn
| cfg r s d :=
  let p := RecParserFn.run p (termPrattParser cfg.pTables) in
  p cfg.toParserConfig r s d

def parseExpr (rbp : Nat) : CommandParserFn :=
TermParserFn.run (RecParserFn.recurse rbp)

end Parser
-- end Lean
