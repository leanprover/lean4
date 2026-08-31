/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.PrettyPrinter.Formatter
public import Lean.PrettyPrinter.Parenthesizer
import Lean.Parser

/-!
# TOML Parser Utilities

Generic parser utilities used by Lake's TOML parser.
-/

namespace Lake.Toml

open Lean Parser PrettyPrinter Formatter Parenthesizer

public def isBinDigit (c : Char) : Bool :=
  c == '0' || c == '1'

public def isOctDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '7'

public def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

public def skipFn : ParserFn := fun _ s => s

public scoped instance : AndThen ParserFn where
  andThen p q := fun c s => let s := p c s; if s.hasError then s else q () c s

/-- `ParserFn` combinator that runs `f` with the current position. -/
@[always_inline, inline] public def usePosFn (f : String.Pos.Raw → ParserFn) : ParserFn :=
  fun c s => f s.pos c s

/-- Match an arbitrary parser or do nothing. -/
public def optFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let s := p c s
  if s.hasError && s.pos == iniPos then s.restore iniSz iniPos else  s

/-- A sequence of `n` repetitions of a parser function. -/
@[inline] public def repeatFn (n : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let rec @[specialize] loop
    | 0, s => s
    | n+1, s =>
      let s := p c s
      if s.hasError then s else loop n s
  loop n s

public def mkUnexpectedCharError (s : ParserState) (c : Char)  (expected : List String := []) (pushMissing := true) : ParserState :=
  s.mkUnexpectedError s!"unexpected '{c}'" expected pushMissing

@[inline] public def satisfyFn (p : Char → Bool) (expected : List String := [])  : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s.mkEOIError expected
  else
    let curr := c.get' i h
    if p curr then
      s.next' c i h
    else
      mkUnexpectedCharError s curr expected

public def takeWhile1Fn (p : Char → Bool) (expected : List String := []) : ParserFn :=
  satisfyFn p expected >> takeWhileFn p

/-- Consume a single digit (i.e., `Char.isDigit`). -/
public def digitFn (expected : List String := ["digit"]) : ParserFn :=
  satisfyFn Char.isDigit expected

/-- Consume a two digits (i.e., `Char.isDigit`). -/
public def digitPairFn (expected := ["digit"]) : ParserFn :=
  digitFn expected >> digitFn expected

/-- Consume a single matching character. -/
public def chFn (c : Char) (expected : List String := [s!"'{c}'"]) : ParserFn :=
  satisfyFn (fun d => d == c) expected

public partial def strAuxFn (str : String) (expected : List String) (strPos : String.Pos.Raw) : ParserFn := fun c s =>
  if h₁ : strPos.atEnd str then
    s
  else
    let s := chFn (strPos.get' str h₁) expected c s
    if s.hasError then s else strAuxFn str expected (strPos.next' str h₁) c s

/-- Consume a matching string atomically. -/
public def strFn (str : String) (expected : List String := [s!"'{str}'"]) : ParserFn :=
  atomicFn <| strAuxFn str expected 0

mutual

public partial def sepByChar1AuxFn (p : Char → Bool) (sep : Char) (expected : List String := []) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s
  else
    let curr := c.get' i h
    if p curr then
      sepByChar1AuxFn p sep expected c (s.next' c i h)
    else if curr == sep then
      sepByChar1Fn p sep expected c (s.next' c i h)
    else
      s

public partial def sepByChar1Fn (p : Char → Bool) (sep : Char) (expected : List String := []) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then
    s
  else
    let curr := c.get' i h
    let s := s.next' c i h
    if p curr then
      sepByChar1AuxFn p sep expected c s
    else if curr == sep then
      s.mkUnexpectedError s!"unexpected separator '{curr}'" expected
    else
      mkUnexpectedCharError s curr expected

end

/-- Push a new atom onto the syntax stack. -/
public def pushAtom (startPos : String.Pos.Raw) (trailingFn := skipFn) : ParserFn := fun c s =>
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let val      := c.extract startPos stopPos
  let s        := trailingFn c s
  let stopPos' := s.pos
  let trailing := c.substring (startPos := stopPos) (stopPos := stopPos')
  let atom     := mkAtom (SourceInfo.original leading startPos trailing (startPos + val)) val
  s.pushSyntax atom

/-- Match an arbitrary `ParserFn` and return the consumed String in a `Syntax.atom`. -/
public def atomFn (p : ParserFn) (trailingFn := skipFn) : ParserFn := fun c s =>
  let startPos := s.pos
  let s := p c s
  if s.hasError then s else
  pushAtom startPos trailingFn c s

public def atom (p : ParserFn) (trailingFn := skipFn) : Parser where
  fn := atomFn p trailingFn

open Formatter Syntax.MonadTraverser in
@[combinator_formatter atom] public def atom.formatter (_ _ : ParserFn) : Formatter := do
  let stx ← getCur
  let .atom info val := stx
    | trace[PrettyPrinter.format.backtrack] "unexpected syntax '{format stx}', expected atom"
      throwBacktrack
  withMaybeTag (getExprPos? stx) (pushToken info val false)
  goLeft

@[combinator_parenthesizer atom]
def atom.parenthesizer (_  _ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Parse a single character as an atom. -/
public def chAtom (c : Char) (expected := [s!"'{c}'"]) (trailingFn := skipFn) : Parser :=
  atom (chFn c expected) trailingFn

@[combinator_formatter chAtom]
public def chAtom.formatter (c : Char) (_ : List String) (_ : ParserFn) : Formatter :=
  rawCh.formatter c

@[combinator_parenthesizer chAtom]
public def chAtom.parenthesizer (_ : Char) (_  : List String) (_ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Parse the trimmed string as an atom (but use the full string for formatting). -/
public def strAtom (s : String) (expected := [s!"'{s}'"]) (trailingFn := skipFn) : Parser :=
  atom (strFn s.trimAscii.copy expected) trailingFn

@[combinator_formatter strAtom]
public def strAtom.formatter (s : String) (_ : List String) (_ : ParserFn) : Formatter :=
  symbolNoAntiquot.formatter s

@[combinator_parenthesizer strAtom]
public def strAtom.parenthesizer (_ : String) (_  : List String) (_ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

/-- Push `(Syntax.node kind <new-atom>)` onto the syntax stack. -/
public def pushLit (kind : SyntaxNodeKind) (startPos : String.Pos.Raw) (trailingFn := skipFn) : ParserFn := fun c s =>
  let stopPos   := s.pos
  let leading   := c.mkEmptySubstringAt startPos
  let val       := c.extract startPos stopPos
  let s         := trailingFn c s
  let wsStopPos := s.pos
  let trailing  := c.substring (startPos := stopPos) (stopPos := wsStopPos)
  let info      := SourceInfo.original leading startPos trailing stopPos
  s.pushSyntax (Syntax.mkLit kind val info)

public def litFn (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let s := p c s
  if s.hasError then s else
  pushLit kind iniPos trailingFn c s

public def lit (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) : Parser where
  fn := litFn kind p trailingFn

@[combinator_formatter lit, expose]
public def lit.formatter (kind : SyntaxNodeKind) (_ _ : ParserFn) : Formatter :=
  visitAtom kind

@[combinator_parenthesizer lit, expose]
public def lit.parenthesizer (_ : SyntaxNodeKind) (_ _ : ParserFn) : Parenthesizer :=
  Parenthesizer.visitToken

@[run_parser_attribute_hooks]
public def litWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserFn) (trailingFn := skipFn) (anonymous := false) : Parser :=
  withAntiquot (mkAntiquot name kind anonymous) $ lit kind p trailingFn

@[inline] public def epsilon (fn : ParserFn) : Parser :=
  {fn := fn, info := epsilonInfo}

@[combinator_formatter epsilon, expose]
public def epsilon.formatter (_ : ParserFn) : Formatter := pure ()

@[combinator_parenthesizer epsilon, expose]
public def epsilon.parenthesizer (_ : ParserFn) : Parenthesizer := pure ()

@[specialize]
partial def modifyTailInfo (f : SourceInfo → SourceInfo) : (stx : Syntax) → Syntax
  | .atom info val => .atom (f info) val
  | .ident info rawVal val pre => .ident (f info) rawVal val pre
  | .node info k args =>
    .node info k <| args.modify (args.size - 1) (modifyTailInfo f)
  | s => s

public def extendTrailingFn (p : ParserFn) : ParserFn := fun c s =>
  let s := p c s
  let stopPos := s.pos
  let tail := s.stxStack.back
  let s := s.popSyntax -- try for linearity
  let tail := modifyTailInfo (stx := tail) fun
    | .original leading pos trailing endPos =>
      .original leading pos {trailing with stopPos} endPos
    | info => info
  s.pushSyntax tail

@[run_parser_attribute_hooks]
public def trailing (p : ParserFn) : Parser :=
  epsilon (extendTrailingFn p)

public def dynamicNode (p : ParserFn) : Parser where
  fn := p

@[combinator_formatter dynamicNode, expose]
public def dynamicNode.formatter (_ : ParserFn) : Formatter := do
  formatterForKind (← Syntax.MonadTraverser.getCur).getKind

@[combinator_parenthesizer dynamicNode, expose]
public def dynamicNode.parenthesizer (_ : ParserFn) : Parenthesizer := do
  parenthesizerForKind (← Syntax.MonadTraverser.getCur).getKind

partial def recNodeFn (f : Parser → Parser) : ParserFn :=
  f (dynamicNode (recNodeFn f)) |>.fn

/--
`Parser → Parser` hidden by an `abbrev`.
Prevents the formatter/parenthesizer generator from transforming it.
-/
public abbrev ParserMapFn := Parser → Parser

@[run_parser_attribute_hooks]
public def recNode (f : ParserMapFn) : Parser :=
  dynamicNode (recNodeFn f)

@[run_parser_attribute_hooks]
public def recNodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (f : ParserMapFn) (anonymous := false) : Parser :=
  withCache kind $ withAntiquot (mkAntiquot name kind anonymous true) $ recNode go
where
  go p := withCache kind $ withAntiquot (mkAntiquot name kind anonymous true) $ f p

@[run_parser_attribute_hooks, inline]
public def sepByLinebreak (p : Parser) (allowTrailingLinebreak := true) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  sepByNoAntiquot p (checkLinebreakBefore >> pushNone) allowTrailingLinebreak

@[run_parser_attribute_hooks, inline]
public def sepBy1Linebreak (p : Parser) (allowTrailingLinebreak := true) : Parser :=
  let p := withAntiquotSpliceAndSuffix `sepBy p (symbol "*")
  sepBy1NoAntiquot p (checkLinebreakBefore >> pushNone) allowTrailingLinebreak

public def skipInsideQuotFn (p : ParserFn) : ParserFn := fun c s =>
  if c.quotDepth > 0 then s else p c s

@[run_parser_attribute_hooks]
public def skipInsideQuot (p : Parser) : Parser :=
  withFn skipInsideQuotFn p
