/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude
public import Lean.Parser.Types
public import Lean.DocString.Syntax
meta import Lean.DocString.Syntax

namespace Lean.Doc.Parser

open Lean Parser
open Lean.Doc.Syntax

local instance : Coe Char ParserFn where
  coe := chFn

partial def atLeastAux (n : Nat) (p : ParserFn) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  let mut s  := p c s
  if s.hasError then
    return if iniPos == s.pos && n == 0 then s.restore iniSz iniPos else s
  if iniPos == s.pos then
    return s.mkUnexpectedError "invalid 'atLeast' parser combinator application, parser did not consume anything"
  if s.stackSize > iniSz + 1 then
    s := s.mkNode nullKind iniSz
  atLeastAux (n - 1) p c s

def atLeastFn (n : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atLeastAux n p c s
  s.mkNode nullKind iniSz

def skipFn : ParserFn := fun _ s => s

def eatSpaces := takeWhileFn (· == ' ')

def repFn : Nat → ParserFn → ParserFn
  | 0, _ => skipFn
  | n+1, p => p >> repFn n p

/-- Like `satisfyFn`, but no special handling of EOI -/
partial def satisfyFn' (p : Char → Bool)
    (errorMsg : String := "unexpected character") :
    ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkUnexpectedError errorMsg
  else if p (c.get' i h) then s.next' c i h
  else s.mkUnexpectedError errorMsg

partial def atMostAux (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s => Id.run do
  let iniSz  := s.stackSize
  let iniPos := s.pos
  if n == 0 then return notFollowedByFn p msg c s
  let mut s := p c s
  if s.hasError then
    return if iniPos == s.pos then s.restore iniSz iniPos else s
  if iniPos == s.pos then
    return s.mkUnexpectedError "invalid 'atMost' parser combinator application, parser did not consume anything"
  if s.stackSize > iniSz + 1 then
    s := s.mkNode nullKind iniSz
  atMostAux (n - 1) p msg c s

def atMostFn (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atMostAux n p msg c s
  s.mkNode nullKind iniSz

/-- Like `satisfyFn`, but allows any escape sequence through -/
partial def satisfyEscFn (p : Char → Bool)
    (errorMsg : String := "unexpected character") :
    ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else if c.get' i h == '\\' then
    let s := s.next' c i h
    let i := s.pos
    if h : c.atEnd i then s.mkEOIError
    else s.next' c i h
  else if p (c.get' i h) then s.next' c i h
  else s.mkUnexpectedError errorMsg

partial def takeUntilEscFn (p : Char → Bool) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s
  else if c.get' i h == '\\' then
    let s := s.next' c i h
    let i := s.pos
    if h : c.atEnd i then s.mkEOIError
    else takeUntilEscFn p c (s.next' c i h)
  else if p (c.get' i h) then s
  else takeUntilEscFn p c (s.next' c i h)

partial def takeWhileEscFn (p : Char → Bool) : ParserFn := takeUntilEscFn (not ∘ p)

def ignoreFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s' := p c s
  s'.shrinkStack iniSz

def withInfoSyntaxFn (p : ParserFn) (infoP : SourceInfo → ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let startPos := s.pos
  let s := p c s
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let trailing := c.mkEmptySubstringAt stopPos
  let info     := SourceInfo.original leading startPos trailing stopPos
  infoP info c (s.shrinkStack iniSz)

def unescapeStr (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.iter
  while !iter.atEnd do
    let c := iter.curr
    iter := iter.next
    if c == '\\' then
      if !iter.atEnd then
        out := out.push iter.curr
        iter := iter.next
    else
      out := out.push c
  out

private def asStringAux (quoted : Bool) (startPos : String.Pos) (transform : String → String) : ParserFn := fun c s =>
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let val      := c.extract startPos stopPos
  let val      := transform val
  let trailing := c.mkEmptySubstringAt stopPos
  let atom     :=
    .atom (SourceInfo.original leading startPos trailing stopPos) <|
      if quoted then val.quote else val
  s.pushSyntax atom

/-- Match an arbitrary Parser and return the consumed String in a `Syntax.atom`. -/
def asStringFn (p : ParserFn) (quoted := false) (transform : String → String := id ) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux quoted startPos transform c (s.shrinkStack iniSz)

def checkCol0Fn (errorMsg : String) : ParserFn := fun c s =>
  let pos      := c.fileMap.toPosition s.pos
  if pos.column = 1 then s
  else s.mkError errorMsg

def _root_.Lean.Parser.ParserContext.currentColumn (c : ParserContext) (s : ParserState) : Nat :=
  c.fileMap.toPosition s.pos |>.column

def pushColumn : ParserFn := fun c s =>
  let col := c.fileMap.toPosition s.pos |>.column
  s.pushSyntax <| Syntax.mkLit `column (toString col) (SourceInfo.synthetic s.pos s.pos)

def guardColumn (p : Nat → Bool) (message : String) : ParserFn := fun c s =>
  if p (c.currentColumn s) then s else s.mkErrorAt message s.pos

def guardMinColumn (min : Nat) : ParserFn :=
  guardColumn (· ≥ min) s!"expected column at least {min}"

def withCurrentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
  p (c.currentColumn s) c s

def bol : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then s else s.mkErrorAt s!"beginning of line at {position}" s.pos

def bolThen (p : ParserFn) (description : String) : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then
    let s := p c s
    if s.hasError then
      s.mkErrorAt description s.pos
    else s
  else s.mkErrorAt description s.pos

/--
We can only start a nestable block if we're immediately after a newline followed by a sequence of
nestable block openers
-/
def onlyBlockOpeners : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let lineStart := c.fileMap.lineStart position.line
  let ok : Bool := Id.run do
    let mut iter := {c.inputString.iter with i := lineStart}
    while iter.i < s.pos && iter.hasNext && iter.i < c.endPos do
      if iter.curr.isDigit then
        while iter.curr.isDigit && iter.i < s.pos && iter.hasNext do
          iter := iter.next
        if !iter.hasNext then return false
        else if iter.curr == '.' || iter.curr == ')' then iter := iter.next
      else if iter.curr == ' ' then iter := iter.next
      else if iter.curr == '>' then iter := iter.next
      else if iter.curr == '*' then iter := iter.next
      else if iter.curr == '+' then iter := iter.next
      else if iter.curr == '-' then iter := iter.next
      else return false
    true

  if ok then s
  else s.mkErrorAt s!"beginning of line or sequence of nestable block openers at {position}" s.pos

def nl := satisfyFn (· == '\n') "newline"

def fakeAtom (str : String) (info : SourceInfo := SourceInfo.none) : ParserFn := fun _c s =>
  let atom := .atom info str
  s.pushSyntax atom

def pushMissing : ParserFn := fun _c s =>
  s.pushSyntax .missing

def strFn (str : String) : ParserFn := asStringFn <| fun c s =>
  let rec go (iter : String.Iterator) (s : ParserState) :=
    if iter.atEnd then s
    else
      let ch := iter.curr
      go iter.next <| satisfyFn (· == ch) ch.toString c s
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := go str.iter s
  if s.hasError then s.mkErrorAt s!"'{str}'" iniPos (some iniSz) else s

public inductive OrderedListType where
   /-- Items like 1. -/
  | numDot
   /-- Items like 1) -/
  | parenAfter
deriving Repr, BEq, DecidableEq

public instance : Ord OrderedListType where
  compare
    | .numDot, .numDot => .eq
    | .numDot, .parenAfter => .lt
    | .parenAfter, .numDot => .gt
    | .parenAfter, .parenAfter => .eq

def OrderedListType.all : List OrderedListType :=
  [.numDot, .parenAfter]

theorem OrderedListType.all_complete : ∀ x : OrderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor

public inductive UnorderedListType where
   /-- Items like * -/
  | asterisk
   /-- Items like - -/
  | dash
   /-- Items like + -/
  | plus
deriving Repr, BEq, DecidableEq

public instance : Ord UnorderedListType where
  compare
    | .asterisk, .asterisk => .eq
    | .asterisk, _ => .lt
    | .dash, .asterisk => .gt
    | .dash, .dash => .eq
    | .dash, .plus => .lt
    | .plus, .plus => .eq
    | .plus, _ => .gt

def UnorderedListType.all : List UnorderedListType :=
  [.asterisk, .dash, .plus]

theorem UnorderedListType.all_complete : ∀ x : UnorderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor

def unorderedListIndicator (type : UnorderedListType) : ParserFn :=
  asStringFn <|
    match type with
    | .asterisk => chFn '*'
    | .dash => chFn '-'
    | .plus => chFn '+'

def orderedListIndicator (type : OrderedListType) : ParserFn :=
  asStringFn <|
    takeWhile1Fn (·.isDigit) "digits" >>
    match type with
    | .numDot => chFn '.'
    | .parenAfter => chFn ')'

def blankLine : ParserFn := nodeFn `blankLine <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> nl

def bullet := atomicFn (go UnorderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (unorderedListIndicator x)
    | x :: xs => atomicFn (unorderedListIndicator x) <|> go xs

def numbering := atomicFn (go OrderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (orderedListIndicator x)
    | x :: xs => atomicFn (orderedListIndicator x) <|> go xs

def inlineTextChar : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else
    let curr := c.get' i h
    match curr with
    | '\\' =>
      let s := s.next' c i h
      let i := s.pos
      if h : c.atEnd i then s.mkEOIError
      else s.next' c i h
    | '*' | '_' | '\n' | '[' | ']' | '{' | '}' | '`' => s.mkUnexpectedErrorAt s!"'{curr}'" i
    | '!' =>
      let s := s.next' c i h
      let i' := s.pos
      if h : c.atEnd i' then s
      else if c.get' i' h == '['
      then s.mkUnexpectedErrorAt "![" i
      else s
    | '$' =>
      let s := s.next' c i h
      let i' := s.pos
      if h : c.atEnd i' then
        s
      else if c.get' i' h == '`' then
        s.mkUnexpectedErrorAt "$`" i
      else if c.get' i' h == '$' then
        let s := s.next' c i' h
        let i' := s.pos
        if h : c.atEnd i' then
          s
        else if c.get' i' h == '`' then
          s.mkUnexpectedErrorAt "$$`" i
        else s
      else s
    | _ => s.next' c i h

/-- Return some inline text up to the next inline opener or the end of
the line, whichever is first. Always consumes at least one
logical character on success, taking escaping into account. -/
def inlineText : ParserFn := asStringFn (transform := unescapeStr) <| atomicFn inlineTextChar >> manyFn inlineTextChar

/-- Block opener prefixes -/
def blockOpener := atomicFn <|
  takeWhileEscFn (· == ' ') >>
  (atomicFn ((bullet >> chFn ' ')) <|>
   atomicFn ((numbering >> chFn ' ')) <|>
   atomicFn (strFn ": ") <|>
   atomicFn (atLeastFn 3 (chFn ':')) <|>
   atomicFn (atLeastFn 3 (chFn '`')) <|>
   atomicFn (strFn "%%%") <|>
   atomicFn (chFn '>'))

def val : ParserFn := fun c s =>
  if h : c.atEnd s.pos then
    s.mkEOIError
  else
    let ch := c.get' s.pos h
    let i := s.stackSize
    if ch == '\"' then
      let s := strLitFnAux s.pos false c (s.next' c s.pos h)
      s.mkNode ``arg_str i
    else if isIdFirst ch || isIdBeginEscape ch then
      let s := rawIdentFn (includeWhitespace := false) c s
      s.mkNode ``arg_ident i
    else if ch.isDigit then
      let s := numberFnAux false c s
      s.mkNode ``arg_num i
    else
      s.mkError "expected identifier, string, or number"

def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Match the character indicated, pushing nothing to the stack in case of success -/
def skipChFn (c : Char) : ParserFn :=
  satisfyFn (· == c) c.toString

def skipToNewline : ParserFn :=
    takeUntilFn (· == '\n')

def skipToSpace : ParserFn :=
    takeUntilFn (· == ' ')

def skipRestOfLine : ParserFn :=
    skipToNewline >> (eoiFn <|> nl)

def skipBlock : ParserFn :=
  skipToNewline >> manyFn nonEmptyLine >> takeWhileFn (· == '\n')
where
  nonEmptyLine : ParserFn :=
    atomicFn <|
      chFn '\n' >>
      takeWhileFn (fun c => c.isWhitespace && c != '\n') >>
      satisfyFn (!·.isWhitespace) "non-whitespace" >> skipToNewline

def recoverBlock (p : ParserFn) (final : ParserFn := skipFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn skipBlock >> final

def recoverBlockWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipBlock >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

def recoverLine (p : ParserFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn skipRestOfLine

def recoverWs (p : ParserFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn <| takeUntilFn (fun c =>  c == ' ' || c == '\n')

def recoverNonSpace (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn (takeUntilFn (fun c => c != ' ')) >>
    show ParserFn from
      fun _ s => s.shrinkStack rctx.initialSize

def recoverWsWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn <| takeUntilFn (fun c =>  c == ' ' || c == '\n') >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

def recoverEol (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => ignoreFn <| skipToNewline

def recoverEolWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipToNewline >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

def recoverSkip (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => skipFn

def recoverSkipWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

/-- Recovers from an error by pushing the provided syntax items, without adjusting the position. -/
def recoverHereWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore rctx.initialSize rctx.initialPos) (·.pushSyntax ·)

def recoverHereWithKeeping (stxs : Array Syntax) (keep : Nat) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore (rctx.initialSize + keep) rctx.initialPos) (·.pushSyntax ·)

def arg : ParserFn :=
    withCurrentStackSize fun iniSz =>
      flag <|> withParens iniSz <|> potentiallyNamed iniSz <|> (val >> mkAnon iniSz)
where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.named iniSz
  mkNamedNoParen (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.named_no_paren iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.anon iniSz
  mkIdent (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.arg_ident iniSz
  flag : ParserFn :=
    nodeFn ``Doc.Syntax.flag_on
      (asStringFn (strFn  "+") >> recoverNonSpace noSpace >> recoverWs (rawIdentFn (includeWhitespace := false))) <|>
    nodeFn ``Doc.Syntax.flag_off
      (asStringFn (strFn "-") >> recoverNonSpace noSpace >> recoverWs (rawIdentFn (includeWhitespace := false)))
  noSpace : ParserFn := fun c s =>
    if h : c.atEnd s.pos then s
    else
      let ch := c.get' s.pos h
      if ch == ' ' then
        s.mkError "no space before"
      else s
  potentiallyNamed iniSz :=
      atomicFn (rawIdentFn (includeWhitespace := false)) >> eatSpaces >>
       ((atomicFn (asStringFn <| strFn ":=") >> eatSpaces >> val >> eatSpaces >> mkNamedNoParen iniSz) <|> (mkIdent iniSz >> mkAnon iniSz))
  withParens iniSz :=
    atomicFn (asStringFn <| strFn "(") >> eatSpaces >>
    recoverWs (rawIdentFn (includeWhitespace := false))  >> eatSpaces >>
    recoverWs (asStringFn <| strFn ":=") >> eatSpaces >>
    recoverWs val >> eatSpaces >>
    recoverEol (asStringFn <| strFn ")") >> eatSpaces >>
    mkNamed iniSz

/--

Skip whitespace for name and arguments. If the argument is `none`,
it's in a single-line context and whitespace may only be the space
character. If it's `some N`, then newlines are allowed, but `N` is the
minimum indentation column.
-/
def nameArgWhitespace : (multiline : Option Nat) → ParserFn
  | none => eatSpaces
  | some n => takeWhileFn (fun c => c == ' ' || c == '\n') >> guardMinColumn n

def args (multiline : Option Nat := none) : ParserFn :=
  sepByFn true arg (nameArgWhitespace multiline)

def nameAndArgs (multiline : Option Nat := none) : ParserFn :=
  nameArgWhitespace multiline >> rawIdentFn (includeWhitespace := false) >>
  nameArgWhitespace multiline >> args (multiline := multiline)

structure InlineCtxt where
  allowNewlines := true
  -- The minimum indentation of a continuation line for the current paragraph
  minIndent : Nat := 0
  -- How many asterisks introduced the current level of boldness? `none` means no bold here.
  boldDepth : Option Nat := none
  -- How many underscores introduced the current level of emphasis? `none` means no emphasis here.
  emphDepth : Option Nat := none

  -- Are we in a link?
  inLink : Bool := false

deriving Inhabited

/- Parsing inlines:
 * Inline parsers may not consume trailing whitespace, and must be robust in the face of leading whitespace
-/

/--
A linebreak that isn't a block break (that is, there's non-space content on the next line)
-/
def linebreak (ctxt : InlineCtxt) : ParserFn :=
  if ctxt.allowNewlines then
    nodeFn ``linebreak <|
      andthenFn (withInfoSyntaxFn skip.fn (fun info => fakeAtom "line!" info)) <|
        nodeFn strLitKind <|
        asStringFn (quoted := true) <|
          atomicFn (chFn '\n' >> lookaheadFn (manyFn (chFn ' ') >> notFollowedByFn (chFn '\n' <|> blockOpener) "newline"))
  else
    errorFn "Newlines not allowed here"

mutual
  partial def emphLike (name : SyntaxNodeKind) (char : Char) (what plural : String) (getter : InlineCtxt → Option Nat) (setter : InlineCtxt → Option Nat → InlineCtxt) (ctxt : InlineCtxt) : ParserFn :=
    nodeFn name <|
    withCurrentColumn fun c =>
      atomicFn (asStringFn (asStringFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      (recoverSkip <|
        withCurrentColumn fun c' =>
          let count := c' - c
          manyFn (inline (setter ctxt (some count))) >>
          asStringFn (atomicFn (noSpaceBefore >> repFn count (satisfyFn (· == char) s!"'{tok count}'"))))

  where
    tok (count : Nat) : String := ⟨List.replicate count char⟩
    opener (ctxt : InlineCtxt) : ParserFn :=
      match getter ctxt with
      | none => many1Fn (satisfyFn (· == char) s!"any number of {char}s")
      | some 1 | some 0 => fun _ s => s.mkError s!"Can't {what} here"
      | some d => atMostFn (d - 1) (satisfyFn (· == char) s!"{char}") s!"at most {d} {plural}"
    noSpaceBefore : ParserFn := fun c s =>
      if s.pos == 0 then s
      else
        let prior := c.get (c.prev s.pos)
        if prior.isWhitespace then
          s.mkError s!"'{char}' without preceding space"
        else s

  partial def emph := emphLike ``emph '_' "emphasize" "underscores" (·.emphDepth) ({· with emphDepth := ·})
  partial def bold := emphLike ``bold '*' "bold" "asterisks" (·.boldDepth) ({· with boldDepth := ·})

  partial def code : ParserFn :=
    nodeFn ``code <|
    withCurrentColumn fun c =>
      atomicFn opener >>
      ( atomicFn <|
        withCurrentColumn fun c' =>
          let count := c' - c
          recoverCode <|
            nodeFn strLitKind
              (asStringFn (many1Fn <| codeContentsFn (count - 1)) (quoted := true) >>
               normFn) >>
            closer count)
  where
    opener : ParserFn := asStringFn (many1Fn (satisfyFn (· == '`') s!"any number of backticks"))
    closer (count : Nat) : ParserFn :=
      asStringFn (atomicFn (repFn count (satisfyFn' (· == '`') s!"expected '{String.mk (.replicate count '`')}' to close inline code"))) >>
      notFollowedByFn (satisfyFn (· == '`') "`") "backtick"
    takeBackticksFn : Nat → ParserFn
      | 0 => satisfyFn (fun _ => false)
      | n+1 => optionalFn (chFn '`' >> takeBackticksFn n)
    recoverCode (p : ParserFn) : ParserFn :=
      recoverFn p fun rctx =>
        (show ParserFn from fun _ s => s.restore rctx.initialSize rctx.initialPos) >>
        atomicFn (nodeFn strLitKind (asStringFn (takeWhileFn (· ≠ '\n')) true) >> ignoreFn (chFn '\n' <|> eoiFn) >> pushMissing)
    codeContentsFn (maxCount : Nat) : ParserFn :=
      atomicFn (asStringFn (satisfyFn (maxCount > 0 && · == '`') >> atMostFn (maxCount - 1) (chFn '`') s!"at most {maxCount} backticks")) <|>
      satisfyFn (· != '`') "expected character other than backtick ('`')"
    normFn : ParserFn := fun _c s => Id.run <| do
      let str := s.stxStack.back
      if let .atom info str := str then
        if str.startsWith "\" " && str.endsWith " \"" then
          let core := str.drop 2 |>.dropRight 2
          if core.any (· != ' ') then
            let str := "\"" ++ core ++ "\""
            let info : SourceInfo :=
              match info with
              | .none => .none
              | .synthetic start stop c => .synthetic (start + ⟨1⟩) (stop - ⟨1⟩) c
              | .original leading start trailing stop =>
                .original
                  {leading with stopPos := leading.stopPos + ⟨1⟩} (start + ⟨1⟩)
                  {trailing with startPos := trailing.startPos - ⟨1⟩} (stop - ⟨1⟩)
            return s.popSyntax.pushSyntax (.atom info str)
      return s

    takeContentsFn (maxCount : Nat) : ParserFn := fun c s =>
      let i := s.pos
      if h : c.atEnd i then s.mkEOIError
      else
        let ch := c.get' i h
        let s := s.next' c i h
        let i := s.pos
        if ch == '\\' then
          if h : c.atEnd i then s.mkEOIError
          else
            let ch := c.get' i h
            let s := s.next' c i h
            if ch ∈ ['`', '\\'] then takeContentsFn maxCount c s
            else
              s.mkError "expected 'n', '\\', or '`'"
        else if ch == '`' then
          optionalFn (atomicFn (takeBackticksFn maxCount) >> takeContentsFn maxCount) c s
        else if ch == '\n' then
          s.mkError "unexpected newline"
        else takeContentsFn maxCount c s

  partial def math : ParserFn :=
    atomicFn (nodeFn ``display_math <| strFn "$$" >> code) <|>
    atomicFn (nodeFn ``inline_math <| strFn "$" >> code)

  -- Read a prefix of a line of text, stopping at a text-mode special character
  partial def text :=
    nodeFn ``text <|
      nodeFn strLitKind <|
        asStringFn (transform := unescapeStr) (quoted := true) <|
          many1Fn inlineTextChar

  partial def link (ctxt : InlineCtxt) :=
    nodeFn ``link <|
      (atomicFn (notInLink ctxt >> strFn "[" >> notFollowedByFn (chFn '^') "'^'" )) >>
      (recoverEol <|
        many1Fn (inline {ctxt with inLink := true}) >>
        strFn "]" >> linkTarget)

  partial def footnote (ctxt : InlineCtxt) :=
    nodeFn ``footnote <|
      (atomicFn (notInLink ctxt >> strFn "[^" )) >>
      (recoverLine <|
        nodeFn `str (asStringFn (quoted := true) (many1Fn (satisfyEscFn (fun c => c != ']' && c != '\n') "other than ']' or newline"))) >>
        strFn "]")

  partial def linkTarget := ref <|> url
  where
    notUrlEnd := satisfyEscFn (· ∉ ")\n".toList) "not ')' or newline" >> takeUntilEscFn (· ∈ ")\n".toList)
    notRefEnd := satisfyEscFn (· ∉ "]\n".toList) "not ']' or newline" >> takeUntilEscFn (· ∈ "]\n".toList)
    ref : ParserFn :=
      nodeFn ``Syntax.ref <|
        (atomicFn <| strFn "[") >>
        recoverEol (nodeFn strLitKind (asStringFn notRefEnd (quoted := true)) >> strFn "]")
    url : ParserFn :=
      nodeFn ``Syntax.url <|
        (atomicFn <| strFn "(") >>
        recoverEol (nodeFn strLitKind (asStringFn notUrlEnd (quoted := true)) >> strFn ")")

  partial def notInLink (ctxt : InlineCtxt) : ParserFn := fun _ s =>
      if ctxt.inLink then s.mkError "Already in a link" else s

  partial def image : ParserFn :=
    nodeFn ``image <|
      atomicFn (strFn "![") >>
      (recoverSkip <|
        nodeFn strLitKind (asStringFn (takeUntilEscFn (· ∈ "]\n".toList)) (quoted := true)) >>
        strFn "]" >>
        linkTarget)

  partial def role (ctxt : InlineCtxt) : ParserFn :=
    nodeFn ``role <|
      intro >> (bracketed <|> atomicFn nonBracketed)
  where
    intro := atomicFn (chFn '{') >> recoverBlock (eatSpaces >> nameAndArgs >> eatSpaces >> chFn '}')
    bracketed := atomicFn (chFn '[') >> recoverBlock (manyFn (inline ctxt) >> chFn ']')
    fakeOpen := .atom SourceInfo.none "["
    fakeClose := .atom SourceInfo.none "]"
    nonBracketed : ParserFn := fun c s =>
      let s := s.pushSyntax fakeOpen
      let s := nodeFn nullKind (delimitedInline ctxt) c s
      s.pushSyntax fakeClose

  partial def delimitedInline (ctxt : InlineCtxt) : ParserFn := emph ctxt <|> bold ctxt <|> code <|> math <|> role ctxt <|> image <|> link ctxt <|> footnote ctxt

  partial def inline (ctxt : InlineCtxt) : ParserFn :=
    text <|> linebreak ctxt <|> delimitedInline ctxt
end

def textLine (allowNewlines := true) : ParserFn := many1Fn (inline { allowNewlines })

open Lean.Parser.Term in
meta def metadataBlock : ParserFn :=
  nodeFn ``metadata_block <|
    opener >>
    metadataContents.fn >>
    takeWhileFn (·.isWhitespace) >>
    closer
where
  opener := atomicFn (bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)") >> eatSpaces >> ignoreFn (chFn '\n')
  closer := bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)" >> eatSpaces >> ignoreFn (chFn '\n' <|> eoiFn)

public structure InList where
  indentation : Nat
  type : OrderedListType ⊕ UnorderedListType
deriving Repr

public structure BlockCtxt where
  minIndent : Nat := 0
  maxDirective : Option Nat := none
  inLists : List InList := []
deriving Inhabited, Repr

def lookaheadOrderedListIndicator (ctxt : BlockCtxt) (p : OrderedListType → Int → ParserFn) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let s := (onlyBlockOpeners >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
    if s.hasError then s.setPos iniPos |>.shrinkStack iniSz
    else
    let numPos := s.pos
    let s := ignoreFn (takeWhile1Fn (·.isDigit) "digits") c s
    if s.hasError then {s with pos := iniPos}.shrinkStack iniSz else
    let digits := c.extract numPos s.pos
    match digits.toNat? with
    | none => {s.mkError s!"digits, got '{digits}'" with pos := iniPos}
    | some n =>
      let i := s.pos
      if h : c.atEnd i then {s.mkEOIError with pos := iniPos}
      else
        let (s, next, type) := match c.get' i h with
          | '.' => (s.next' c i h, (chFn ' ' <|> chFn '\n'), OrderedListType.numDot)
          | ')' => (s.next' c i h, (chFn ' ' <|> chFn '\n'), OrderedListType.parenAfter)
          | other => (s.setError {unexpected := s!"unexpected '{other}'", expected := ["'.'", "')'"]}, skipFn, .numDot)
        if s.hasError then {s with pos := iniPos}
        else
          let s := next c s
          if s.hasError then {s with pos := iniPos}
          else
            let leading := c.mkEmptySubstringAt numPos
            let trailing := c.mkEmptySubstringAt i
            let num := Syntax.mkNumLit digits (info := .original leading numPos trailing i)
            p type n c (s.shrinkStack iniSz |>.setPos numPos |>.pushSyntax num)

def lookaheadUnorderedListIndicator (ctxt : BlockCtxt) (p : UnorderedListType → ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := (onlyBlockOpeners >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
  let bulletPos := s.pos
  if s.hasError then s.setPos iniPos |>.shrinkStack iniSz
  else if h : c.atEnd s.pos then s.mkEOIError.setPos iniPos |>.shrinkStack iniSz
  else let (s, type) : (_ × UnorderedListType) := match c.get' s.pos h with
    | '*' => (s.next' c s.pos h, .asterisk)
    | '-' => (s.next' c s.pos h, .dash)
    | '+' => (s.next' c s.pos h, .plus)
    | other => (s.setError {expected := ["*", "-", "+"], unexpected := s!"'{other}'"}, .plus)
  if s.hasError then s.setPos iniPos
  else
    let s := (chFn ' ' <|> chFn '\n') c s
    if s.hasError then s.setPos iniPos
    else p type c (s.shrinkStack iniSz |>.setPos bulletPos)

def skipUntilDedent (indent : Nat) : ParserFn :=
  skipRestOfLine >>
  manyFn (chFn ' ' >> takeWhileFn (· == ' ') >> guardColumn (· ≥ indent) s!"indentation at {indent}" >> skipRestOfLine)

def recoverUnindent (indent : Nat) (p : ParserFn) (finish : ParserFn := skipFn) : ParserFn := recoverFn p (fun _ => ignoreFn (skipUntilDedent indent) >> finish)

mutual
  partial def listItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``li (bulletFn >> withCurrentColumn fun c => ignoreFn (manyFn (chFn ' ' <|> chFn '\n')) >> blocks1 {ctxt with minIndent := c})
  where
    bulletFn :=
      match ctxt.inLists.head? with
      | none => fun _ s => s.mkError "not in a list"
      | some ⟨col, .inr type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          unorderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' ' <|> chFn '\n'))
      | some ⟨col, .inl type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          orderedListIndicator type >> ignoreFn (lookaheadFn (chFn ' ' <|> chFn '\n'))

  partial def descItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``desc <|
      colonFn >>
      withCurrentColumn fun c => textLine >> ignoreFn (manyFn blankLine) >>
      fakeAtom "=>" >>
      takeWhileFn (· == ' ') >>
      recoverSkip (guardColumn (· ≥ c) s!"indentation at least {c}" >>
        blocks1 { ctxt with minIndent := c}) >>
      ignoreFn (manyFn blankLine)
  where
    colonFn := atomicFn <|
      takeWhileFn (· == ' ') >>
      guardColumn (· == ctxt.minIndent) s!"indentation at {ctxt.minIndent}" >>
      asStringFn (chFn ':' false) >> ignoreFn (lookaheadFn (chFn ' '))

  partial def blockquote (ctxt : BlockCtxt) : ParserFn :=
    atomicFn <| nodeFn ``blockquote <|
      takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> chFn '>' >>
      withCurrentColumn fun c => blocks { ctxt with minIndent := c }

  partial def unorderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ul <|
      lookaheadUnorderedListIndicator ctxt fun type =>
        withCurrentColumn fun c =>
          fakeAtom "ul{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inr type⟩  :: ctxt.inLists}) >>
          fakeAtom "}"

  partial def orderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ol <|
      fakeAtom "ol(" >>
      lookaheadOrderedListIndicator ctxt fun type _start => -- TODO? Validate list numbering?
        withCurrentColumn fun c =>
          fakeAtom ")" >> fakeAtom "{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inl type⟩  :: ctxt.inLists}) >>
          fakeAtom "}"

  partial def definitionList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``dl <|
      atomicFn (onlyBlockOpeners >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn ':' >> chFn ' ')) >> guardMinColumn ctxt.minIndent) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "dl{" info) >>
      withCurrentColumn (fun c => many1Fn (descItem {ctxt with minIndent := c})) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "}" info)

  partial def para (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``para <|
      atomicFn (takeWhileFn (· == ' ') >> notFollowedByFn blockOpener "block opener" >> guardMinColumn ctxt.minIndent) >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "para{" (info := info)) >>
      textLine >>
      withInfoSyntaxFn skip.fn (fun info => fakeAtom "}" (info := info))

  partial def header (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``header <|
      guardMinColumn ctxt.minIndent >>
      atomicFn (bol >>
        withCurrentColumn fun c =>
          withInfoSyntaxFn (many1Fn (skipChFn '#')) (fun info => fakeAtom "header(" (info := info)) >>
          withCurrentColumn fun c' =>
            skipChFn ' ' >> takeWhileFn (· == ' ') >> lookaheadFn (satisfyFn (· != '\n') "non-newline") >>
            (show ParserFn from fun _ s => s.pushSyntax <| Syntax.mkNumLit (toString <| c' - c - 1)) >>
            fakeAtom ")") >>
      fakeAtom "{" >>
      textLine (allowNewlines := false) >>
      fakeAtom "}"

  partial def codeBlock (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``codeblock <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >> asStringFn (atLeastFn 3 (skipChFn '`'))) >>
        withIndentColumn fun c =>
          recoverUnindent c <|
            withCurrentColumn fun c' =>
              let fenceWidth := c' - c
              takeWhileFn (· == ' ') >>
              optionalFn nameAndArgs >>
              asStringFn (satisfyFn (· == '\n') "newline") >>
              nodeFn strLitKind (asStringFn (manyFn (atomicFn blankLine <|> codeFrom c fenceWidth)) (transform := deIndent c) (quoted := true)) >>
              closeFence c fenceWidth
  where
    withIndentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
      let colStx := s.stxStack.get! (s.stxStack.size - 2)
      match colStx with
      | .node _ `column #[.atom _ col] =>
        if let some colNat := col.toNat? then
          let opener := s.stxStack.get! (s.stxStack.size - 1)
          p colNat c (s.popSyntax.popSyntax.pushSyntax opener)
        else
          s.mkError s!"Internal error - not a Nat {col}"
      | other => s.mkError s!"Internal error - not a column node {other}"

    deIndent (n : Nat) (str : String) : String := Id.run do
      let str := if str != "" && str.back == '\n' then str.dropRight 1 else str
      let mut out := ""
      for line in str.splitOn "\n" do
        out := out ++ line.drop n ++ "\n"
      out

    codeFrom (col width : Nat) :=
      atomicFn (bol >> takeWhileFn (· == ' ') >> guardMinColumn col >>
        notFollowedByFn (atLeastFn width (skipChFn '`')) "ending fence") >>
      manyFn (satisfyFn (· != '\n') "non-newline") >> satisfyFn (· == '\n') "newline"

    closeFence (col width : Nat) :=
      bol >> takeWhileFn (· == ' ') >> guardColumn (· == col) s!"column {col}" >>
      atomicFn (asStringFn (repFn width (skipChFn '`'))) >>
      notFollowedByFn (skipChFn '`') "extra `" >>
      takeWhileFn (· == ' ') >> (satisfyFn (· == '\n') "newline" <|> eoiFn)

  partial def directive (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``directive <|
      -- Opener - leaves indent info and open token on the stack
      atomicFn
        (eatSpaces >> guardMinColumn ctxt.minIndent >>
          asStringFn (atLeastFn 3 (skipChFn ':')) >>
         guardOpenerSize >>
         eatSpaces >>
         recoverEolWith #[.missing, .node .none nullKind #[]] (nameAndArgs >> satisfyFn (· == '\n') "newline")) >>
       fakeAtom "\n" >>
       ignoreFn (manyFn blankLine) >>
        (withFencePos 3 fun ⟨l, col⟩ =>
          withFenceSize 3 fun fenceWidth =>
            blocks {ctxt with minIndent := col, maxDirective := fenceWidth} >>
            recoverHereWith #[.missing]
              (closeFence l fenceWidth >>
               withFence 0 fun info _ c s =>
                if (c.fileMap.toPosition info.getPos?.get!).column != col then
                  s.mkErrorAt s!"closing '{String.mk <| List.replicate fenceWidth ':'}' from directive on line {l} at column {col}, but it's at column {(c.fileMap.toPosition info.getPos?.get!).column}" info.getPos?.get!
                else
                  s))

  where
    withFence (atDepth : Nat) (p : SourceInfo → String → ParserFn) : ParserFn := fun c s =>
        match s.stxStack.get! (s.stxStack.size - (atDepth + 1)) with
        | .atom info str =>
          if str.all (· == ':') then
            p info str c s
          else
            s.mkError s!"Internal error - index {atDepth} wasn't the directive fence - it was the atom {str}"
        | .missing => s.pushSyntax .missing
        | stx =>
          s.mkError s!"Internal error - index {atDepth} wasn't the directive fence - it was {stx} in {s.stxStack.back}, {s.stxStack.pop.back}, {s.stxStack.pop.pop.back}, {s.stxStack.pop.pop.pop.back}"

    withFenceSize (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withFence atDepth fun _ str => p str.length

    withFencePos (atDepth : Nat) (p : Position → ParserFn) : ParserFn :=
      withFence atDepth fun info _ c s => p (c.fileMap.toPosition info.getPos?.get!) c s

    withIndentColumn (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withFence atDepth fun info _ c s =>
        let col := c.fileMap.toPosition info.getPos?.get! |>.column
        p col c s

    guardOpenerSize : ParserFn := withFenceSize 0 fun x =>
        if let some m := ctxt.maxDirective then
          if x < m then skipFn else fun _ s => s.mkError "Too many ':'s here"
        else skipFn

    closeFence (line width : Nat) :=
      let str := String.mk (.replicate width ':')
      bolThen (description := s!"closing '{str}' for directive from line {line}")
        (eatSpaces >>
         asStringFn (strFn str) >> notFollowedByFn (chFn ':') "':'" >>
         eatSpaces >>
         (ignoreFn <| atomicFn (satisfyFn (· == '\n') "newline") <|> eoiFn))

  -- This low-level definition is to get exactly the right amount of lookahead
  -- together with column tracking
  partial def block_command (ctxt : BlockCtxt) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let restorePosOnErr : ParserState → ParserState
      | ⟨stack, lhsPrec, _, cache, some msg, errs⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg, errs⟩
      | other => other
    let s := eatSpaces c s
    if s.hasError then restorePosOnErr s
    else
      let s := (intro >> eatSpaces >> ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)) c s
      if s.hasError then restorePosOnErr s
      else
        s.mkNode ``Syntax.command iniSz
  where
    eatSpaces := takeWhileFn (· == ' ')
    intro := guardMinColumn (ctxt.minIndent) >> atomicFn (chFn '{') >> nameAndArgs >> nameArgWhitespace none >> chFn '}'

  partial def linkRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``link_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> chFn '[' >> nodeFn strLitKind (asStringFn (quoted := true) (nameStart >> manyFn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      nodeFn strLitKind (asStringFn (quoted := true) (takeWhileFn (· != '\n'))) >>
      ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)
  where nameStart := satisfyEscFn (fun c => c != ']' && c != '^') "not ']' or '^'"

  partial def footnoteRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``footnote_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> strFn "[^" >> nodeFn strLitKind (asStringFn (quoted := true) (many1Fn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      notFollowedByFn blockOpener "block opener" >> guardMinColumn c.minIndent >> textLine

  public partial def block (c : BlockCtxt) : ParserFn :=
    block_command c <|> unorderedList c <|> orderedList c <|> definitionList c <|> header c <|> codeBlock c <|> directive c <|> blockquote c <|> linkRef c <|> footnoteRef c <|> para c <|> metadataBlock

  public partial def blocks (c : BlockCtxt) : ParserFn := sepByFn true (block c) (ignoreFn (manyFn blankLine))

  public partial def blocks1 (c : BlockCtxt) : ParserFn := sepBy1Fn true (block c) (ignoreFn (manyFn blankLine))

  public partial def document (blockContext : BlockCtxt := {}) : ParserFn := ignoreFn (manyFn blankLine) >> blocks blockContext
end
