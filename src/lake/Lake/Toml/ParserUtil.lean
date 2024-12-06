/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Parser
import Lean.PrettyPrinter.Formatter

/-!
# TOML Parser Utilities

Generic parser utilities used by Lake's TOML parser.
-/

namespace Lake.Toml

open Lean Parser PrettyPrinter Formatter

def isBinDigit (c : Char) : Bool :=
  c == '0' || c == '1'

def isOctDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def skipFn : ParserFn := fun _ s => s

scoped instance : AndThen ParserFn where
  andThen p q := fun c s => let s := p c s; if s.hasError then s else q () c s

/-- `ParserFn` combinator that runs `f` with the current position. -/
@[always_inline, inline] def usePosFn (f : String.Pos → ParserFn) : ParserFn :=
  fun c s => f s.pos c s

/-- Match an arbitrary parser or do nothing. -/
def optFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s := p c s
  if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else  s

/-- A sequence of `n` repetitions of a parser function. -/
@[inline] def repeatFn (n : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let rec @[specialize] loop
    | 0, s => s
    | n+1, s =>
      let s := p c s
      if s.hasError then s else loop n s
  loop n s

def mkUnexpectedCharError (s : ParserState) (c : Char)  (expected : List String := []) (pushMissing := true) : ParserState :=
  s.mkUnexpectedError s!"unexpected '{c}'" expected pushMissing

@[inline] def satisfyFn (p : Char → Bool) (expected : List String := [])  : ParserFn := fun c s =>
  let i := s.pos
  if h : c.input.atEnd i then
    s.mkEOIError expected
  else
    let curr := c.input.get' i h
    if p curr then
      s.next' c.input i h
    else
      mkUnexpectedCharError s curr expected

def takeWhile1Fn (p : Char → Bool) (expected : List String := []) : ParserFn :=
  satisfyFn p expected >> takeWhileFn p

/-- Consume a single digit (i.e., `Char.isDigit`). -/
def digitFn (expected : List String := ["digit"]) : ParserFn :=
  satisfyFn Char.isDigit expected

/-- Consume a two digits (i.e., `Char.isDigit`). -/
def digitPairFn (expected := ["digit"]) : ParserFn :=
  digitFn expected >> digitFn expected

/-- Consume a single matching character. -/
def chFn (c : Char) (expected : List String := [s!"'{c}'"]) : ParserFn :=
  satisfyFn (fun d => d == c) expected

partial def strAuxFn (str : String) (expected : List String) (strPos : String.Pos) : ParserFn := fun c s =>
  if h₁ : str.atEnd strPos then
    s
  else
    let s := chFn (str.get' strPos h₁) expected c s
    if s.hasError then s else strAuxFn str expected (str.next' strPos h₁) c s

/-- Consume a matching string atomically. -/
def strFn (str : String) (expected : List String := [s!"'{str}'"]) : ParserFn :=
  atomicFn <| strAuxFn str expected 0

mutual

partial def sepByChar1AuxFn (p : Char → Bool) (sep : Char) (expected : List String := []) : ParserFn := fun c s =>
  let i := s.pos
  let input := c.input
  if h : input.atEnd i then
    s
  else
    let curr := input.get' i h
    if p curr then
      sepByChar1AuxFn p sep expected c (s.next' input i h)
    else if curr == sep then
      sepByChar1Fn p sep expected c (s.next' input i h)
    else
      s

partial def sepByChar1Fn (p : Char → Bool) (sep : Char) (expected : List String := []) : ParserFn := fun c s =>
  let i := s.pos
  let input := c.input
  if h : input.atEnd i then
    s
  else
    let curr := input.get' i h
    let s := s.next' input i h
    if p curr then
      sepByChar1AuxFn p sep expected c s
    else if curr == sep then
      s.mkUnexpectedError s!"unexpected separator '{curr}'" expected
    else
      mkUnexpectedCharError s curr expected

end

/-- Push a new atom onto the syntax stack. -/
def pushAtom (startPos : String.Pos) (trailingFn := skipFn) : ParserFn := fun c s =>
  let input    := c.input
  let stopPos  := s.pos
  let leading  := mkEmptySubstringAt input startPos
  let val      := input.extract startPos stopPos
  let s        := trailingFn c s
  let stopPos' := s.pos
  let trailing := { str := input, startPos := stopPos, stopPos := stopPos' : Substring }
  let atom     := mkAtom (SourceInfo.original leading startPos trailing (startPos + val)) val
  s.pushSyntax atom

/-- Match an arbitrary `ParserFn` and return the consumed String in a `Syntax.atom`. -/
def atomFn (p : ParserFn) (trailingFn := skipFn) : ParserFn := fun c s =>
  let startPos := s.pos
  let s := p c s
  if s.hasError then s else
  pushAtom startPos trailingFn c s

def atom (p : ParserFn) (trailingFn := skipFn) : Parser where
  fn := atomFn p trailingFn

def getInfoExprPos? : SourceInfo → Option String.Pos
  | SourceInfo.synthetic (pos := pos) .. => pos
  | _ => none

def getSyntaxExprPos? : Syntax → Option String.Pos
  | .node info _ _ => getInfoExprPos? info
  | .atom info _ => getInfoExprPos? info
  | .ident info _ _ _ => getInfoExprPos? info
  | .missing => none

open Formatter Syntax.MonadTraverser in
@[combinator_formatter atom] def atom.formatter (_ _ : ParserFn) : Formatter := do
  let stx ← getCur
  let .atom info val := stx
    | trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected atom"
      throwBacktrack
  withMaybeTag (getSyntaxExprPos? stx) (pushToken info val false)
  goLeft

@[combinator_parenthesizer atom]
def atom.parenthesizer (_  _ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Parse a single character as an atom. -/
def chAtom (c : Char) (expected := [s!"'{c}'"]) (trailingFn := skipFn) : Parser :=
  atom (chFn c expected) trailingFn

@[combinator_formatter chAtom]
def chAtom.formatter (c : Char) (_ : List String) (_ : ParserFn) : Formatter :=
  rawCh.formatter c

@[combinator_parenthesizer chAtom]
def chAtom.parenthesizer (_ : Char) (_  : List String) (_ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Parse the trimmed string as an atom (but use the full string for formatting). -/
def strAtom (s : String) (expected := [s!"'{s}'"]) (trailingFn := skipFn) : Parser :=
  atom (strFn s.trim expected) trailingFn

@[combinator_formatter strAtom]
def strAtom.formatter (s : String) (_ : List String) (_ : ParserFn) : Formatter :=
  symbolNoAntiquot.formatter s

@[combinator_parenthesizer strAtom]
def strAtom.parenthesizer (_ : String) (_  : List String) (_ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Push `(Syntax.node kind <new-atom>)` onto the syntax stack. -/
def pushLit (kind : SyntaxNodeKind) (startPos : String.Pos) (trailingFn := skipFn) : ParserFn := fun c s =>
  let input     := c.input
  let stopPos   := s.pos
  let leading   := mkEmptySubstringAt input startPos
  let val       := input.extract startPos stopPos
  let s         := trailingFn c s
  let wsStopPos := s.pos
  let trailing  := { str := input, startPos := stopPos, stopPos := wsStopPos : Substring }
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit kind val info)

def litFn (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let s := p c s
  if s.hasError then s else
  pushLit kind iniPos trailingFn c s

def lit (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) : Parser where
  fn := litFn kind p trailingFn

@[combinator_formatter lit]
def lit.formatter (kind : SyntaxNodeKind) (_ _ : ParserFn) : Formatter :=
  visitAtom kind

@[combinator_parenthesizer lit]
def lit.parenthesizer (_ : SyntaxNodeKind) (_ _ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

def litWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) (anonymous := false) : Parser :=
  withAntiquot (mkAntiquot name kind anonymous) $ lit kind p trailingFn

@[inline] def epsilon (fn : ParserFn) : Parser :=
  {fn := fn, info := epsilonInfo}

@[combinator_formatter epsilon]
def epsilon.formatter (_ : ParserFn) : Formatter := pure ()

@[combinator_parenthesizer epsilon]
def epsilon.parenthesizer (_ : ParserFn) : Parenthesizer := pure ()

def SourceInfo.updateTrailing (trailing : Substring) : SourceInfo → SourceInfo
  | SourceInfo.original leading pos _ endPos => SourceInfo.original leading pos trailing endPos
  | info                                     => info

partial def modifyTailInfo (f : SourceInfo → SourceInfo) : (stx : Syntax) → Syntax
  | .atom info val => .atom (f info) val
  | .ident info rawVal val pre => .ident (f info) rawVal val pre
  | .node info k args =>
    .node info k <| args.modify (args.size - 1) (modifyTailInfo f)
  | s => s

def extendTrailingFn (p : ParserFn) : ParserFn := fun c s =>
  let s := p c s
  let stopPos := s.pos
  let tail := s.stxStack.back
  let s := s.popSyntax -- try for linearity
  let tail := modifyTailInfo (stx := tail) fun
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos} endPos
    | info => info
  s.pushSyntax tail

def trailing (p : ParserFn) : Parser :=
  epsilon (extendTrailingFn p)

def dynamicNode (p : ParserFn) : Parser where
  fn := p

@[combinator_formatter dynamicNode]
def dynamicNode.formatter (_ : ParserFn) : Formatter := do
  formatterForKind (← Syntax.MonadTraverser.getCur).getKind

@[combinator_parenthesizer dynamicNode]
def dynamicNode.parenthesizer (_ : ParserFn) : Parenthesizer := do
  Parenthesizer.parenthesizerForKind (← Syntax.MonadTraverser.getCur).getKind

partial def recNodeFn (f : Parser → Parser) : ParserFn :=
  f (dynamicNode (recNodeFn f)) |>.fn

/--
`Parser → Parser` hidden by an `abbrev`.
Prevents the formatter/parenthesizer generator from transforming it.
-/
abbrev ParserMapFn := Parser → Parser

def recNode (f : ParserMapFn) : Parser :=
  dynamicNode (recNodeFn f)

def recNodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (f : ParserMapFn) (anonymous := false) : Parser :=
  withCache kind $ withAntiquot (mkAntiquot name kind anonymous true) $ recNode go
where
  go p := withCache kind $ withAntiquot (mkAntiquot name kind anonymous true) $ f p

@[inline] def sepByLinebreak (p : Parser) (allowTrailingLinebreak := true) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  sepByNoAntiquot p (checkLinebreakBefore >> pushNone) allowTrailingLinebreak

@[inline] def sepBy1Linebreak (p : Parser) (allowTrailingLinebreak := true) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  sepBy1NoAntiquot p (checkLinebreakBefore >> pushNone) allowTrailingLinebreak

def skipInsideQuotFn (p : ParserFn) : ParserFn := fun c s =>
  if c.quotDepth > 0 then s else p c s

@[run_parser_attribute_hooks] def skipInsideQuot (p : Parser) : Parser :=
  withFn skipInsideQuotFn p
