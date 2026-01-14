import init.lean.message init.lean.parser.syntax init.lean.parser.trie init.lean.parser.basic init.lean.parser.stringliteral
import init.lean.parser.token

namespace Lean
namespace flatParser
open String
open Parser (Syntax Syntax.missing)
open Parser (Trie TokenMap)

abbreviation pos := String.Pos

/-- A precomputed cache for quickly mapping Char offsets to positions. -/
structure FileMap :=
(offsets : Array Nat)
(lines   : Array Nat)

namespace FileMap
private def fromStringAux (s : String) : Nat → Nat → Nat → pos → Array Nat → Array Nat → FileMap
| 0     offset line i offsets lines := ⟨offsets.push offset, lines.push line⟩
| (k+1) offset line i offsets lines :=
  if s.atEnd i then ⟨offsets.push offset, lines.push line⟩
  else let c := s.get i in
       let i := s.next i in
       let offset := offset + 1 in
       if c = '\n'
       then fromStringAux k offset (line+1) i (offsets.push offset) (lines.push (line+1))
       else fromStringAux k offset line i offsets lines

def fromString (s : String) : FileMap :=
fromStringAux s s.length 0 1 0 (Array.empty.push 0) (Array.empty.push 1)

/- Remark: `offset is in [(offsets.get b), (offsets.get e)]` and `b < e` -/
private def toPositionAux (offsets : Array Nat) (lines : Array Nat) (offset : Nat) : Nat → Nat → Nat → Position
| 0     b e := ⟨offset, 1⟩ -- unreachable
| (k+1) b e :=
  let offsetB := offsets.get b in
  if e = b + 1 then ⟨offset - offsetB, lines.get b⟩
  else let m := (b + e) / 2 in
       let offsetM := offsets.get m in
       if offset = offsetM then ⟨0, lines.get m⟩
       else if offset > offsetM then toPositionAux k m e
       else toPositionAux k b m

def toPosition : FileMap → Nat → Position
| ⟨offsets, lines⟩ offset := toPositionAux offsets lines offset offsets.size 0 (offsets.size-1)
end FileMap

structure TokenConfig :=
(«prefix» : String)
(lbp : Nat := 0)

structure FrontendConfig :=
(filename : String)
(input    : String)
(FileMap : FileMap)

/- Remark: if we have a Node in the Trie with `some TokenConfig`, the String induced by the path is equal to the `TokenConfig.prefix`. -/
structure ParserConfig extends FrontendConfig :=
(tokens : Trie TokenConfig)

-- Backtrackable State
structure ParserState :=
(messages : MessageLog)

structure TokenCacheEntry :=
(startPos stopPos : pos)
(tk : Syntax)

-- Non-backtrackable State
structure ParserCache :=
(tokenCache : Option TokenCacheEntry := none)

inductive Result (α : Type)
| ok       (a : α)        (i : pos) (cache : ParserCache) (State : ParserState) (eps : Bool) : Result
| error {} (msg : String) (i : pos) (cache : ParserCache) (stx : Syntax)         (eps : Bool) : Result

inductive Result.IsOk {α : Type} : Result α → Prop
| mk (a : α) (i : pos) (cache : ParserCache) (State : ParserState) (eps : Bool) : Result.IsOk (Result.ok a i cache State eps)

theorem errorIsNotOk {α : Type} {msg : String} {i : pos} {cache : ParserCache} {stx : Syntax} {eps : Bool}
                        (h : Result.IsOk (@Result.error α msg i cache stx eps)) : False :=
match h with end

@[inline] def unreachableError {α β : Type} {msg : String} {i : pos} {cache : ParserCache} {stx : Syntax} {eps : Bool}
                                (h : Result.IsOk (@Result.error α msg i cache stx eps)) : β :=
False.elim (errorIsNotOk h)

def resultOk := {r : Result Unit // r.IsOk}

@[inline] def mkResultOk (i : pos) (cache : ParserCache) (State : ParserState) (eps := true) : resultOk :=
⟨Result.ok () i cache State eps, Result.IsOk.mk _ _ _ _ _⟩

def parserCoreM (α : Type) :=
ParserConfig → resultOk → Result α
abbreviation parserCore := parserCoreM Syntax

structure recParsers :=
(cmdParser  : parserCore)
(termParser : Nat → parserCore)

def parserM (α : Type) := recParsers → parserCoreM α
abbreviation Parser := parserM Syntax
abbreviation trailingParser := Syntax → Parser

@[inline] def command.Parser : Parser := λ ps, ps.cmdParser
@[inline] def Term.Parser (rbp : Nat := 0) : Parser  := λ ps, ps.termParser rbp

@[inline] def parserM.pure {α : Type} (a : α) : parserM α :=
λ _ _ r,
  match r with
  | ⟨Result.ok _ it c s _, h⟩   := Result.ok a it c s true
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline_if_reduce] def eagerOr  (b₁ b₂ : Bool) := b₁ || b₂
@[inline_if_reduce] def eagerAnd (b₁ b₂ : Bool) := b₁ && b₂

@[inline] def parserM.bind {α β : Type} (x : parserM α) (f : α → parserM β) : parserM β :=
λ ps cfg r,
  match x ps cfg r with
  | Result.ok a i c s e₁ :=
    (match f a ps cfg (mkResultOk i c s) with
     | Result.ok b i c s e₂        := Result.ok b i c s (eagerAnd e₁ e₂)
     | Result.error msg i c stx e₂ := Result.error msg i c stx (eagerAnd e₁ e₂))
  | Result.error msg i c stx e  := Result.error msg i c stx e

instance : Monad parserM :=
{pure := @parserM.pure, bind := @parserM.bind}

@[inline] protected def orelse {α : Type} (p q : parserM α) : parserM α :=
λ ps cfg r,
  match r with
  | ⟨Result.ok _ i₁ _ s₁ _, _⟩ :=
    (match p ps cfg r with
     | Result.error msg₁ i₂ c₂ stx₁ true := q ps cfg (mkResultOk i₁ c₂ s₁)
     | other                           := other)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] protected def failure {α : Type} : parserM α :=
λ _ _ r,
  match r with
  | ⟨Result.ok _ i c s _, h⟩    := Result.error "failure" i c Syntax.missing true
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

instance : Alternative parserM :=
{ orelse         := @flatParser.orelse,
  failure        := @flatParser.failure,
  ..flatParser.Monad }

def setSilentError {α : Type} : Result α → Result α
| (Result.error i c msg stx _) := Result.error i c msg stx true
| other                        := other

/--
`try p` behaves like `p`, but it pretends `p` hasn't
consumed any input when `p` fails.
-/
@[inline] def try {α : Type} (p : parserM α) : parserM α :=
λ ps cfg r, setSilentError (p ps cfg r)

@[inline] def atEnd (cfg : ParserConfig) (i : pos) : Bool :=
cfg.input.atEnd i

@[inline] def curr (cfg : ParserConfig) (i : pos) : Char :=
cfg.input.get i

@[inline] def next (cfg : ParserConfig) (i : pos) : pos :=
cfg.input.next i

@[inline] def inputSize (cfg : ParserConfig) : Nat :=
cfg.input.length

@[inline] def currPos : resultOk → pos
| ⟨Result.ok _ i _ _ _, _⟩    := i
| ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def currState : resultOk → ParserState
| ⟨Result.ok _ _ _ s _, _⟩    := s
| ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

def mkError {α : Type} (r : resultOk) (msg : String) (stx : Syntax := Syntax.missing) (eps := true) : Result α :=
match r with
| ⟨Result.ok _ i c s _, _⟩    := Result.error msg i c stx eps
| ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[inline] def satisfy (p : Char → Bool) : parserM Char :=
λ _ cfg r,
  match r with
  | ⟨Result.ok _ i ch st e, _⟩ :=
    if atEnd cfg i then mkError r "end of input"
    else let c := curr cfg i in
         if p c then Result.ok c (next cfg i) ch st false
         else mkError r "unexpected character"
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

def any : parserM Char :=
satisfy (λ _, true)

@[specialize] def takeUntilAux (p : Char → Bool) (cfg : ParserConfig) : Nat → resultOk → Result Unit
| 0     r := r.val
| (n+1) r :=
  match r with
  | ⟨Result.ok _ i ch st e, _⟩ :=
    if atEnd cfg i then r.val
    else let c := curr cfg i in
         if p c then r.val
         else takeUntilAux n (mkResultOk (next cfg i) ch st true)
  | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

@[specialize] def takeUntil (p : Char → Bool) : parserM Unit :=
λ ps cfg r, takeUntilAux p cfg (inputSize cfg) r

def takeUntilNewLine : parserM Unit :=
takeUntil (= '\n')

def whitespace : parserM Unit :=
takeUntil (λ c, !c.isWhitespace)

-- setOption Trace.Compiler.boxed True
--- setOption pp.implicit True

def strAux (cfg : ParserConfig) (str : String) (error : String) : Nat → resultOk → pos → Result Unit
| 0     r j := mkError r error
| (n+1) r j :=
  if str.atEnd j then r.val
  else
    match r with
    | ⟨Result.ok _ i ch st e, _⟩ :=
      if atEnd cfg i then Result.error error i ch Syntax.missing true
      else if curr cfg i = str.get j then strAux n (mkResultOk (next cfg i) ch st true) (str.next j)
      else Result.error error i ch Syntax.missing true
    | ⟨Result.error _ _ _ _ _, h⟩ := unreachableError h

-- #exit

@[inline] def str (s : String) : parserM Unit :=
λ ps cfg r, strAux cfg s ("expected " ++ repr s) (inputSize cfg) r 0

@[specialize] def manyAux (p : parserM Unit) : Nat → Bool → parserM Unit
| 0     fst := pure ()
| (k+1) fst := λ ps cfg r,
  let i₀ := currPos r in
  let s₀ := currState r in
  match p ps cfg r with
  | Result.ok a i c s _    := manyAux k false ps cfg (mkResultOk i c s)
  | Result.error _ _ c _ _ := Result.ok () i₀ c s₀ fst

@[inline] def many (p : parserM Unit) : parserM Unit  :=
λ ps cfg r, manyAux p (inputSize cfg) true ps cfg r

@[inline] def many1 (p : parserM Unit) : parserM Unit  :=
p *> many p

def dummyParserCore : parserCore :=
λ cfg r, mkError r "dummy"

def testParser {α : Type} (x : parserM α) (input : String) : String :=
let r :=
  x { cmdParser := dummyParserCore, termParser := λ _, dummyParserCore }
    { filename := "test", input := input, FileMap := FileMap.fromString input, tokens := Lean.Parser.Trie.empty }
    (mkResultOk 0 {} {messages := MessageLog.empty}) in
match r with
| Result.ok _ i _ _ _      := "Ok at " ++ toString i
| Result.error msg i _ _ _ := "Error at " ++ toString i ++ ": " ++ msg

/-
mutual def recCmd, recTerm (parseCmd : Parser) (parseTerm : Nat → Parser) (parseLvl : Nat → parserCore)
with recCmd  : Nat → parserCore
| 0     cfg r := mkError r "Parser: no progress"
| (n+1) cfg r := parseCmd ⟨recCmd n, parseLvl, recTerm n⟩ cfg r
with recTerm : Nat → Nat → parserCore
| 0     rbp cfg r := mkError r "Parser: no progress"
| (n+1) rbp cfg r := parseTerm rbp ⟨recCmd n, parseLvl, recTerm n⟩ cfg r
-/

/-
def runParser (x : Parser) (parseCmd : Parser) (parseLvl : Nat → Parser) (parseTerm : Nat → Parser)
               (input : Iterator) (cfg : ParserConfig) : Result Syntax :=
let it := input in
let n  := it.remaining in
let r  := mkResultOk it {} {messages := MessageLog.Empty} in
let pl := recLvl (parseLvl) n in
let ps : recParsers := { cmdParser  := recCmd parseCmd parseTerm pl n,
                          lvlParser  := pl,
                          termParser := recTerm parseCmd parseTerm pl n } in
x ps cfg r
-/

structure parsingTables :=
(leadingTermParsers : TokenMap Parser)
(trailingTermParsers : TokenMap trailingParser)

abbreviation CommandParserM (α : Type) :=
parsingTables → parserM α

end flatParser
end Lean

section
open Lean.flatParser

def flatP : parserM Unit :=
many1 (str "++" <|> str "**" <|>  (str "--" *> takeUntil (= '\n') *> any *> pure ()))

end

section
open Lean.Parser
open Lean.Parser.MonadParsec

@[reducible] def Parser (α : Type) : Type :=  ReaderT Lean.flatParser.recParsers (ReaderT Lean.flatParser.ParserConfig (ParsecT Syntax (StateT ParserCache Id))) α

def testParsec (p : Parser Unit) (input : String) : String :=
let ps : Lean.flatParser.recParsers := { cmdParser := Lean.flatParser.dummyParserCore, termParser := λ _, Lean.flatParser.dummyParserCore } in
let cfg : Lean.flatParser.ParserConfig := { filename := "test", input := input, FileMap := Lean.flatParser.FileMap.fromString input, tokens := Lean.Parser.Trie.empty } in
let r := p ps cfg input.mkOldIterator {} in
match r with
| (Parsec.Result.ok _ it _, _)   := "OK at " ++ toString it.offset
| (Parsec.Result.error msg _, _) := "Error " ++ msg.toString

@[inline] def str' (s : String) : Parser Unit :=
str s *> pure ()

def parsecP : Parser Unit :=
many1' (str' "++" <|> str' "**" <|> (str "--" *> takeUntil (λ c, c = '\n') *> any *> pure ()))

def parsecP2 : Parser Unit :=
many1' ((parseStringLiteral *> whitespace *> pure ()) <|> (str "--" *> takeUntil (λ c, c = '\n') *> any *> pure ()))

end


namespace BasicParser
open Lean.Parser
open Lean.Parser.MonadParsec

def testBasicParser (p : BasicParserM Unit) (input : String) : String :=
let cfg : Lean.Parser.ParserConfig := {
filename := "test", input := input, fileMap := { lines := {} }, tokens := Lean.Parser.Trie.empty } in
let r := p cfg input.mkOldIterator {} in
match r with
| (Parsec.Result.ok _ it _, _)   := "OK at " ++ toString it.offset
| (Parsec.Result.error msg _, _) := "Error " ++ msg.toString

@[inline] def str' (s : String) : BasicParserM Unit :=
str s *> pure ()

def parserP : BasicParserM Unit :=
many1' (str' "++" <|> str' "**" <|> (str "--" *> takeUntil (λ c, c = '\n') *> any *> pure ()))

def parser2 : BasicParserM Unit :=
many1' ((parseStringLiteral *> Lean.Parser.MonadParsec.whitespace *> pure ()) <|> (str "--" *> takeUntil (λ c, c = '\n') *> any *> pure ()))

def parser3 : BasicParserM Unit :=
Lean.Parser.whitespace

end BasicParser

def mkBigString : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString n (s ++ "-- new comment\n")

def mkBigString2 : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString2 n (s ++ "\"hello\\nworld\"\n-- comment\n")

def mkBigString3 : Nat → String → String
| 0     s := s
| (n+1) s := mkBigString3 n (s ++ "/- /- comment 1 -/ -/ \n -- comment 2 \n \t \n ")

@[noinline] def testFlatP (s : String) : IO Unit :=
IO.println (Lean.flatParser.testParser flatP s)

@[noinline] def testParsecP (p : Parser Unit) (s : String) : IO Unit :=
IO.println (testParsec p s)

@[noinline] def testBasicParser (p : Lean.Parser.BasicParserM Unit) (s : String) : IO Unit :=
IO.println (BasicParser.testBasicParser p s)

@[noinline] def prof {α : Type} (msg : String) (p : IO α) : IO α :=
let msg₁ := "Time for '" ++ msg ++ "':" in
let msg₂ := "Memory usage for '" ++ msg ++ "':" in
allocprof msg₂ (timeit msg₁ p)

def main (xs : List String) : IO Unit :=
-- let s₁ := mkBigString xs.head.toNat "" in
-- let s₂ := s₁ ++ "bad" ++ mkBigString 20 "" in
-- let s₃ := mkBigString2 xs.head.toNat "" in
let s₄ := mkBigString3 xs.head.toNat "" in
-- prof "flat Parser 1" (testFlatP s₁) *>
-- prof "flat Parser 2" (testFlatP s₂) *>
-- prof "Parsec 1" (testParsecP parsecP s₁) *>
-- prof "Parsec 2" (testParsecP parsecP s₂) *>
-- prof "Parsec 3" (testParsecP parsecP2 s₃) *>
prof "Basic parser 1" (testBasicParser BasicParser.parser3 s₄)
