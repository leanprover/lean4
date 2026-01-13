/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude
public import Lean.DocString.Syntax
import Lean.Parser.Term.Basic

set_option linter.missingDocs true

namespace Lean.Doc.Parser

open Lean Parser
open Lean.Doc.Syntax

local instance : Coe Char ParserFn where
  coe := chFn

private partial def atLeastAux (n : Nat) (p : ParserFn) : ParserFn := fun c s => Id.run do
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

private def atLeastFn (n : Nat) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atLeastAux n p c s
  s.mkNode nullKind iniSz

/--
A parser that does nothing.
-/
public def skipFn : ParserFn := fun _ s => s

private def eatSpaces := takeWhileFn (· == ' ')

private def repFn : Nat → ParserFn → ParserFn
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

private partial def atMostAux (n : Nat) (p : ParserFn) (msg : String) : ParserFn :=
  fun c s => Id.run do
    let iniSz  := s.stackSize
    let iniPos := s.pos
    if n == 0 then return notFollowedByFn p msg c s
    let mut s := p c s
    if s.hasError then
      return if iniPos == s.pos then s.restore iniSz iniPos else s
    if iniPos == s.pos then
      return s.mkUnexpectedError "invalid 'atMost' parser combinator application, parser did not \
        consume anything"
    if s.stackSize > iniSz + 1 then
      s := s.mkNode nullKind iniSz
    atMostAux (n - 1) p msg c s

private def atMostFn (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atMostAux n p msg c s
  s.mkNode nullKind iniSz

/-- Like `satisfyFn`, but allows any escape sequence through -/
private partial def satisfyEscFn (p : Char → Bool)
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

private partial def takeUntilEscFn (p : Char → Bool) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s
  else if c.get' i h == '\\' then
    let s := s.next' c i h
    let i := s.pos
    if h : c.atEnd i then s.mkEOIError
    else takeUntilEscFn p c (s.next' c i h)
  else if p (c.get' i h) then s
  else takeUntilEscFn p c (s.next' c i h)

private partial def takeWhileEscFn (p : Char → Bool) : ParserFn := takeUntilEscFn (not ∘ p)

/--
Parses as `p`, but discards the result.
-/
public def ignoreFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s' := p c s
  s'.shrinkStack iniSz


private def withInfoSyntaxFn (p : ParserFn) (infoP : SourceInfo → ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let startPos := s.pos
  let s := p c s
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let trailing := c.mkEmptySubstringAt stopPos
  let info     := SourceInfo.original leading startPos trailing stopPos
  infoP info c (s.shrinkStack iniSz)

private def unescapeStr (str : String) : String := Id.run do
  let mut out := ""
  let mut iter := str.startPos
  while h : ¬iter.IsAtEnd do
    let c := iter.get h
    iter := iter.next h
    if c == '\\' then
      if h : ¬iter.IsAtEnd then
        out := out.push (iter.get h)
        iter := iter.next h
    else
      out := out.push c
  out

private def asStringAux (quoted : Bool) (startPos : String.Pos.Raw) (transform : String → String) :
    ParserFn := fun c s =>
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
public def asStringFn (p : ParserFn) (quoted := false) (transform : String → String := id ) :
    ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asStringAux quoted startPos transform c (s.shrinkStack iniSz)

private def checkCol0Fn (errorMsg : String) : ParserFn := fun c s =>
  let pos      := c.fileMap.toPosition s.pos
  if pos.column = 1 then s
  else s.mkError errorMsg

private def _root_.Lean.Parser.ParserContext.currentColumn
    (c : ParserContext) (s : ParserState) : Nat :=
  c.fileMap.toPosition s.pos |>.column

private def pushColumn : ParserFn := fun c s =>
  let col := c.fileMap.toPosition s.pos |>.column
  s.pushSyntax <| Syntax.mkLit `column (toString col) (SourceInfo.synthetic s.pos s.pos)

private def guardColumn (p : Nat → Bool) (message : String) : ParserFn := fun c s =>
  if p (c.currentColumn s) then s else s.mkErrorAt message s.pos

private def guardMinColumn (min : Nat) : ParserFn :=
  guardColumn (· ≥ min) s!"expected column at least {min}"

private def withCurrentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
  p (c.currentColumn s) c s

private def bol : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let col := position |>.column
  if col == 0 then s else s.mkErrorAt s!"beginning of line at {position}" s.pos

private def bolThen (p : ParserFn) (description : String) : ParserFn := fun c s =>
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
private def onlyBlockOpeners : ParserFn := fun c s =>
  let position := c.fileMap.toPosition s.pos
  let lineStart := c.fileMap.lineStart position.line
  let ok : Bool := Id.run do
    let mut iter := c.inputString.pos! lineStart
    while h : iter.offset < s.pos && ¬iter.IsAtEnd && iter.offset < c.endPos do
      have h : ¬iter.IsAtEnd := by simp at h; exact h.1.2
      if (iter.get h).isDigit then
        while h : ¬iter.IsAtEnd && iter.get!.isDigit && iter.offset < s.pos do
          iter := iter.next (by simp at h; exact h.1.1)
        if h : iter.IsAtEnd then return false
        else if iter.get h == '.' || iter.get h == ')' then iter := iter.next h
      else if iter.get h == ' ' then iter := iter.next h
      else if iter.get h == '>' then iter := iter.next h
      else if iter.get h == '*' then iter := iter.next h
      else if iter.get h == '+' then iter := iter.next h
      else if iter.get h == '-' then iter := iter.next h
      else return false
    true

  if ok then s
  else s.mkErrorAt s!"beginning of line or sequence of nestable block openers at {position}" s.pos

private def nl := satisfyFn (· == '\n') "newline"

/--
Construct a “fake” atom with the given string content and source information.

Normally, atoms are always substrings of the original input; however, Verso's concrete syntax
is different enough from Lean's that this isn't always a good match.
-/
public def fakeAtom (str : String) (info : SourceInfo := SourceInfo.none) : ParserFn := fun _c s =>
  let atom := .atom info str
  s.pushSyntax atom

/--
Construct a “fake” atom with the given string content, with zero-width source information at the
current position.

Normally, atoms are always substrings of the original input; however, Verso's concrete syntax is
different enough from Lean's that this isn't always a good match.
-/
private def fakeAtomHere (str : String) : ParserFn :=
  withInfoSyntaxFn skip.fn (fun info => fakeAtom str (info := info))

private def pushMissing : ParserFn := fun _c s =>
  s.pushSyntax .missing

private def strFn (str : String) : ParserFn := asStringFn <| fun c s =>
  let rec go (iter : str.Pos) (s : ParserState) :=
    if h : iter.IsAtEnd then s
    else
      let ch := iter.get h
      go (iter.next h) <| satisfyFn (· == ch) ch.toString c s
  termination_by iter
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := go str.startPos s
  if s.hasError then s.mkErrorAt s!"'{str}'" iniPos (some iniSz) else s

/--
Ordered lists may have two styles of indicator, with trailing dots or parentheses.
-/
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

private def OrderedListType.all : List OrderedListType :=
  [.numDot, .parenAfter]

private theorem OrderedListType.all_complete : ∀ x : OrderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor

/--
Unordered lists may have three indicators: asterisks, dashes, or pluses.
-/
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

private def UnorderedListType.all : List UnorderedListType :=
  [.asterisk, .dash, .plus]

private theorem UnorderedListType.all_complete : ∀ x : UnorderedListType, x ∈ all := by
  unfold all; intro x; cases x <;> repeat constructor

private def unorderedListIndicator (type : UnorderedListType) : ParserFn :=
  asStringFn <|
    match type with
    | .asterisk => chFn '*'
    | .dash => chFn '-'
    | .plus => chFn '+'

private def orderedListIndicator (type : OrderedListType) : ParserFn :=
  asStringFn <|
    takeWhile1Fn (·.isDigit) "digits" >>
    match type with
    | .numDot => chFn '.'
    | .parenAfter => chFn ')'

private def blankLine : ParserFn :=
  nodeFn `blankLine <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> nl

private def endLine : ParserFn :=
  ignoreFn <| atomicFn <| asStringFn <| takeWhileFn (· == ' ') >> eoiFn

private def bullet := atomicFn (go UnorderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (unorderedListIndicator x)
    | x :: xs => atomicFn (unorderedListIndicator x) <|> go xs

private def numbering := atomicFn (go OrderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (orderedListIndicator x)
    | x :: xs => atomicFn (orderedListIndicator x) <|> go xs

/--
Parses a character that's allowed as part of inline text. This resolves escaped characters and
performs limited lookahead for characters that only begin a different inline as part of a sequence.
-/
public def inlineTextChar : ParserFn := fun c s =>
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
private def inlineText : ParserFn :=
  asStringFn (transform := unescapeStr) <| atomicFn inlineTextChar >> manyFn inlineTextChar

/--
Parses block opener prefixes. At the beginning of the line, if this parser succeeds, then a special
block is beginning.
-/
public def blockOpener := atomicFn <|
  takeWhileEscFn (· == ' ') >>
  (atomicFn ((bullet >> chFn ' ')) <|> -- Unordered list
   atomicFn ((numbering >> chFn ' ')) <|> -- Ordered list
   atomicFn (strFn ": ") <|> -- Description list item
   atomicFn (atLeastFn 3 (chFn ':')) <|> -- Directive
   atomicFn (atLeastFn 3 (chFn '`')) <|> -- Code block
   atomicFn (strFn "%%%") <|> -- Metadata
   atomicFn (chFn '>')) -- Block quote

/-- Parses an argument value, which may be a string literal, identifier, or numeric literal. -/
public def val : ParserFn := fun c s =>
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

private def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Match the character indicated, pushing nothing to the stack in case of success -/
private def skipChFn (c : Char) : ParserFn :=
  satisfyFn (· == c) c.toString

private def skipToNewline : ParserFn :=
    takeUntilFn (· == '\n')

private def skipToSpace : ParserFn :=
    takeUntilFn (· == ' ')

private def skipRestOfLine : ParserFn :=
    skipToNewline >> (eoiFn <|> nl)

private def skipBlock : ParserFn :=
  skipToNewline >> manyFn nonEmptyLine >> takeWhileFn (· == '\n')
where
  nonEmptyLine : ParserFn :=
    atomicFn <|
      chFn '\n' >>
      takeWhileFn (fun c => c.isWhitespace && c != '\n') >>
      satisfyFn (!·.isWhitespace) "non-whitespace" >> skipToNewline

/--
Recovers from a parse error by skipping input until one or more complete blank lines has been
skipped.
-/
public def recoverBlock (p : ParserFn) (final : ParserFn := skipFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn skipBlock >> final

private def recoverBlockWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipBlock >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

private def recoverLine (p : ParserFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn skipRestOfLine

private def recoverWs (p : ParserFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn <| takeUntilFn (fun c =>  c == ' ' || c == '\n')

private def recoverNonSpace (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn (takeUntilFn (fun c => c != ' ')) >>
    show ParserFn from
      fun _ s => s.shrinkStack rctx.initialSize

private def recoverWsWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn <| takeUntilFn (fun c =>  c == ' ' || c == '\n') >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

private def recoverEol (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => ignoreFn <| skipToNewline

private def recoverEolWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    ignoreFn skipToNewline >>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

private def recoverSkip (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => skipFn

private def recoverSkipWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.shrinkStack rctx.initialSize) (·.pushSyntax ·)

/-- Recovers from an error by pushing the provided syntax items, without adjusting the position. -/
def recoverHereWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore rctx.initialSize rctx.initialPos) (·.pushSyntax ·)

private def recoverHereWithKeeping (stxs : Array Syntax) (keep : Nat) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore (rctx.initialSize + keep) rctx.initialPos) (·.pushSyntax ·)

/--
Parses an argument to a role, directive, command, or code block, which may be named or positional or
a flag.
-/
public def arg : ParserFn :=
    withCurrentStackSize fun iniSz =>
      flag <|> withParens iniSz <|> potentiallyNamed iniSz <|> (val >> mkAnon iniSz)
where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.named iniSz
  mkNamedNoParen (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.named_no_paren iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.anon iniSz
  mkIdent (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Syntax.arg_ident iniSz
  flag : ParserFn :=
    nodeFn ``Doc.Syntax.flag_on
      (asStringFn (strFn  "+") >> recoverNonSpace noSpace >>
      recoverWs (rawIdentFn (includeWhitespace := false))) <|>
    nodeFn ``Doc.Syntax.flag_off
      (asStringFn (strFn "-") >> recoverNonSpace noSpace >>
      recoverWs (rawIdentFn (includeWhitespace := false)))
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
private def nameArgWhitespace : (multiline : Option Nat) → ParserFn
  | none => eatSpaces
  | some n => takeWhileFn (fun c => c == ' ' || c == '\n') >> guardMinColumn n

/-- Parses zero or more arguments to a role, directive, command, or code block. -/
public def args (multiline : Option Nat := none) : ParserFn :=
  sepByFn true arg (nameArgWhitespace multiline)

/-- Parses a name and zero or more arguments to a role, directive, command, or code block. -/
public def nameAndArgs (multiline : Option Nat := none) : ParserFn :=
  nameArgWhitespace multiline >> rawIdentFn (includeWhitespace := false) >>
  nameArgWhitespace multiline >> args (multiline := multiline)

/--
The context within which a newline element is parsed.
-/
public structure InlineCtxt where
  /-- Are newlines allowed here? -/
  allowNewlines := true
  /--
  The minimum indentation of a continuation line for the current paragraph
  -/
  minIndent : Nat := 0
  /--
  How many asterisks introduced the current level of boldness? `none` means no bold here.
  -/
  boldDepth : Option Nat := none
  /--
  How many underscores introduced the current level of emphasis? `none` means no emphasis here.
  -/
  emphDepth : Option Nat := none
  /-- Are we in a link? -/
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
      andthenFn (fakeAtomHere "line!") <|
        nodeFn strLitKind <|
        asStringFn (quoted := true) <|
          atomicFn (chFn '\n' >> lookaheadFn (manyFn (chFn ' ') >> notFollowedByFn (chFn '\n' <|> blockOpener) "newline"))
  else
    errorFn "Newlines not allowed here"

private partial def notInLink (ctxt : InlineCtxt) : ParserFn := fun _ s =>
  if ctxt.inLink then s.mkError "Already in a link" else s

mutual
  private partial def emphLike
    (name : SyntaxNodeKind) (char : Char) (what plural : String)
    (getter : InlineCtxt → Option Nat) (setter : InlineCtxt → Option Nat → InlineCtxt)
    (ctxt : InlineCtxt) : ParserFn :=
    nodeFn name <|
    withCurrentColumn fun c =>
      atomicFn (asStringFn (asStringFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      (recoverSkip <|
        withCurrentColumn fun c' =>
          let count := c' - c
          manyFn (inline (setter ctxt (some count))) >>
          asStringFn (atomicFn (noSpaceBefore >> repFn count (satisfyFn (· == char) s!"'{tok count}'"))))

  where
    tok (count : Nat) : String := String.ofList (List.replicate count char)
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

  /--
  Parses emphasis: a matched pair of one or more `_`.
  -/
  public partial def emph :=
    emphLike ``emph '_' "emphasize" "underscores" (·.emphDepth) ({· with emphDepth := ·})

  /--
  Parses bold: a matched pair of one or more `*`.
  -/
  public partial def bold :=
    emphLike ``bold '*' "bold" "asterisks" (·.boldDepth) ({· with boldDepth := ·})

  /--
  Parses inline code.
  -/
  public partial def code : ParserFn :=
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
      asStringFn (atomicFn (repFn count (satisfyFn' (· == '`') s!"expected '{String.ofList (.replicate count '`')}' to close inline code"))) >>
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
          let core := str.drop 2 |>.dropEnd 2 |>.copy
          if core.any (· != ' ') then
            let str := "\"" ++ core ++ "\""
            let info : SourceInfo :=
              match info with
              | .none => .none
              | .synthetic start stop c => .synthetic (start.offsetBy ⟨1⟩) (stop.unoffsetBy ⟨1⟩) c
              | .original leading start trailing stop =>
                .original
                  {leading with stopPos := leading.stopPos.offsetBy ⟨1⟩} (start.offsetBy ⟨1⟩)
                  {trailing with startPos := trailing.startPos.unoffsetBy ⟨1⟩} (stop.unoffsetBy ⟨1⟩)
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

  /--
  Parses mathematics.
  -/
  public partial def math : ParserFn :=
    atomicFn (nodeFn ``display_math <| strFn "$$" >> code) <|>
    atomicFn (nodeFn ``inline_math <| strFn "$" >> code)

  /-- Reads a prefix of a line of text, stopping at a text-mode special character. -/
  public partial def text :=
    nodeFn ``text <|
      nodeFn strLitKind <|
        asStringFn (transform := unescapeStr) (quoted := true) <|
          many1Fn inlineTextChar

  /-- Parses a link. -/
  public partial def link (ctxt : InlineCtxt) :=
    nodeFn ``link <|
      (atomicFn (notInLink ctxt >> strFn "[" >> notFollowedByFn (chFn '^') "'^'" )) >>
      (recoverEol <|
        many1Fn (inline {ctxt with inLink := true}) >>
        strFn "]" >> linkTarget)

  /-- Parses a footnote. -/
  public partial def footnote (ctxt : InlineCtxt) :=
    nodeFn ``footnote <|
      (atomicFn (notInLink ctxt >> strFn "[^" )) >>
      (recoverLine <|
        nodeFn `str (asStringFn (quoted := true) (many1Fn (satisfyEscFn (fun c => c != ']' && c != '\n') "other than ']' or newline"))) >>
        strFn "]")

  private partial def linkTarget := ref <|> url
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

  /-- Parses an image. -/
  public partial def image : ParserFn :=
    nodeFn ``image <|
      atomicFn (strFn "![") >>
      (recoverSkip <|
        nodeFn strLitKind (asStringFn (takeUntilEscFn (· ∈ "]\n".toList)) (quoted := true)) >>
        strFn "]" >>
        linkTarget)

  /-- Parses a role. -/
  public partial def role (ctxt : InlineCtxt) : ParserFn :=
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

  /--
  Parses an inline that is self-delimiting (that is, with well-defined start and stop characters).
  -/
  public partial def delimitedInline (ctxt : InlineCtxt) : ParserFn :=
    emph ctxt <|> bold ctxt <|> code <|> math <|> role ctxt <|> image <|>
    link ctxt <|> footnote ctxt

  /--
  Parses any inline element.
  -/
  public partial def inline (ctxt : InlineCtxt) : ParserFn :=
    text <|> linebreak ctxt <|> delimitedInline ctxt
end

/--
Parses a line of text (that is, one or more inline elements).
-/
def textLine (allowNewlines := true) : ParserFn := many1Fn (inline { allowNewlines })

open Lean.Parser.Term in
/-- A non-`meta` copy of `Lean.Doc.Syntax.metadataContents`. -/
@[run_builtin_parser_attribute_hooks]
public def metadataContents : Parser :=
  structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))

def withPercents : ParserFn → ParserFn := fun p =>
  adaptUncacheableContextFn (fun c => {c with tokens := c.tokens.insert "%%%" "%%%"}) p

open Lean.Parser.Term in
/--
Parses a metadata block, which contains the contents of a Lean structure initialization but is
surrounded by `%%%` on each side.
-/
public def metadataBlock : ParserFn :=
  nodeFn ``metadata_block <|
    opener >>
    withPercents metadataContents.fn >>
    closer
where
  opener := atomicFn (bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)") >> eatSpaces >> ignoreFn (chFn '\n')
  closer := bolThen (eatSpaces >> strFn "%%%") "%%% (at line beginning)" >> eatSpaces >> ignoreFn (chFn '\n' <|> eoiFn)

/--
Records that the parser is presently parsing a list.
-/
public structure InList where
  /-- The indentation of list indicators. -/
  indentation : Nat
  /-- The specific list type and its indicator style -/
  type : OrderedListType ⊕ UnorderedListType
deriving Repr

/--
The context within which a block should be valid.
-/
public structure BlockCtxt where
  /--
  The block's minimum indentation.
  -/
  minIndent : Nat := 0
  /--
  The block's maximal directive size (that is, the greatest number of allowed colons).
  -/
  maxDirective : Option Nat := none
  /--
  The nested list context, innermost first.
  -/
  inLists : List InList := []
deriving Inhabited, Repr

/--
Succeeds when the parser is looking at an ordered list indicator.
-/
public def lookaheadOrderedListIndicator (ctxt : BlockCtxt) (p : OrderedListType → Int → ParserFn) :
    ParserFn := fun c s =>
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
        | other =>
          (s.setError { unexpected := s!"unexpected '{other}'", expected := ["'.'", "')'"] },
           skipFn,
           .numDot)
      if s.hasError then {s with pos := iniPos}
      else
        let s := next c s
        if s.hasError then {s with pos := iniPos}
        else
          let leading := c.mkEmptySubstringAt numPos
          let trailing := c.mkEmptySubstringAt i
          let num := Syntax.mkNumLit digits (info := .original leading numPos trailing i)
          p type n c (s.shrinkStack iniSz |>.setPos numPos |>.pushSyntax num)

/--
Succeeds when the parser is looking at an unordered list indicator.
-/
public def lookaheadUnorderedListIndicator (ctxt : BlockCtxt) (p : UnorderedListType → ParserFn) :
    ParserFn := fun c s =>
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

private def skipUntilDedent (indent : Nat) : ParserFn :=
  skipRestOfLine >>
  manyFn (chFn ' ' >> takeWhileFn (· == ' ') >> guardColumn (· ≥ indent) s!"indentation at {indent}" >> skipRestOfLine)

private def recoverUnindent (indent : Nat) (p : ParserFn) (finish : ParserFn := skipFn) :
    ParserFn :=
  recoverFn p (fun _ => ignoreFn (skipUntilDedent indent) >> finish)

private def blockSep := ignoreFn (manyFn blankLine >> optionalFn endLine)

mutual
  /-- Parses a list item according to the current nesting context. -/
  public partial def listItem (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``li <|
      bulletFn >>
      withCurrentColumn fun c =>
        ignoreFn (manyFn (chFn ' ' <|> chFn '\n')) >> blocks1 {ctxt with minIndent := c}
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

  /-- Parses an item from a description list. -/
  public partial def descItem (ctxt : BlockCtxt) : ParserFn :=
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

  /-- Parses a block quote. -/
  public partial def blockquote (ctxt : BlockCtxt) : ParserFn :=
    atomicFn <| nodeFn ``blockquote <|
      takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> chFn '>' >>
      withCurrentColumn fun c => blocks { ctxt with minIndent := c }

  /-- Parses an unordered list. -/
  public partial def unorderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ul <|
      lookaheadUnorderedListIndicator ctxt fun type =>
        withCurrentColumn fun c =>
          fakeAtomHere "ul{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inr type⟩  :: ctxt.inLists}) >>
          fakeAtomHere "}"

  /-- Parses an ordered list. -/
  public partial def orderedList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``ol <|
      fakeAtomHere "ol(" >>
      lookaheadOrderedListIndicator ctxt fun type _start => -- TODO? Validate list numbering?
        withCurrentColumn fun c =>
          fakeAtomHere ")" >> fakeAtomHere "{" >>
          many1Fn (listItem {ctxt with minIndent := c + 1 , inLists := ⟨c, .inl type⟩  :: ctxt.inLists}) >>
          fakeAtomHere "}"

  /-- Parses a definition list. -/
  public partial def definitionList (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``dl <|
      atomicFn (onlyBlockOpeners >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn ':' >> chFn ' ')) >> guardMinColumn ctxt.minIndent) >>
      fakeAtomHere "dl{" >>
      withCurrentColumn (fun c => many1Fn (descItem {ctxt with minIndent := c})) >>
      fakeAtomHere "}"

  /-- Parses a paragraph (that is, a sequence of otherwise-undecorated inlines). -/
  public partial def para (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``para <|
      atomicFn (takeWhileFn (· == ' ') >> notFollowedByFn blockOpener "block opener" >> guardMinColumn ctxt.minIndent) >>
      fakeAtomHere "para{" >>
      textLine >>
      fakeAtomHere "}"

  /-- Parses a header. -/
  public partial def header (ctxt : BlockCtxt) : ParserFn :=
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
      fakeAtomHere "}"

  /--
  Parses a code block. The resulting string literal has already had the fences' leading indentation
  stripped.
  -/
  public partial def codeBlock (ctxt : BlockCtxt) : ParserFn :=
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
      let str := if str != "" && str.back == '\n' then str.dropEnd 1 |>.copy else str
      let mut out := ""
      for line in str.split '\n' do
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

  /-- Parses a directive. -/
  public partial def directive (ctxt : BlockCtxt) : ParserFn :=
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
                  s.mkErrorAt s!"closing '{String.ofList <| List.replicate fenceWidth ':'}' from directive on line {l} at column {col}, but it's at column {(c.fileMap.toPosition info.getPos?.get!).column}" info.getPos?.get!
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
      let str := String.ofList (.replicate width ':')
      bolThen (description := s!"closing '{str}' for directive from line {line}")
        (eatSpaces >>
         asStringFn (strFn str) >> notFollowedByFn (chFn ':') "':'" >>
         eatSpaces >>
         (ignoreFn <| atomicFn (satisfyFn (· == '\n') "newline") <|> eoiFn))

  /--
  Parses a block command.
  -/
  -- This low-level definition is to get exactly the right amount of lookahead
  -- together with column tracking
  public partial def block_command (ctxt : BlockCtxt) : ParserFn := fun c s =>
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

  /--
  Parses a link reference target.
  -/
  public partial def linkRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``link_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> chFn '[' >> nodeFn strLitKind (asStringFn (quoted := true) (nameStart >> manyFn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      nodeFn strLitKind (asStringFn (quoted := true) (takeWhileFn (· != '\n'))) >>
      ignoreFn (satisfyFn (· == '\n') "newline" <|> eoiFn)
  where nameStart := satisfyEscFn (fun c => c != ']' && c != '^') "not ']' or '^'"

  /--
  Parses a footnote reference target.
  -/
  public partial def footnoteRef (c : BlockCtxt) : ParserFn :=
    nodeFn ``footnote_ref <|
      atomicFn (ignoreFn (bol >> eatSpaces >> guardMinColumn c.minIndent) >> strFn "[^" >> nodeFn strLitKind (asStringFn (quoted := true) (many1Fn (satisfyEscFn (· != ']') "not ']'"))) >> strFn "]:") >>
      eatSpaces >>
      notFollowedByFn blockOpener "block opener" >> guardMinColumn c.minIndent >> textLine

  /--
  Parses a block.
  -/
  public partial def block (c : BlockCtxt) : ParserFn :=
    block_command c <|> unorderedList c <|> orderedList c <|> definitionList c <|> header c <|> codeBlock c <|> directive c <|> blockquote c <|> linkRef c <|> footnoteRef c <|> para c <|> metadataBlock

  /--
  Parses zero or more blocks.
  -/
  public partial def blocks (c : BlockCtxt) : ParserFn := sepByFn true (block c) blockSep

  /--
  Parses one or more blocks.
  -/
  public partial def blocks1 (c : BlockCtxt) : ParserFn := sepBy1Fn true (block c) blockSep

  /--
  Parses some number of blank lines followed by zero or more blocks.
  -/
  public partial def document (blockContext : BlockCtxt := {}) : ParserFn := ignoreFn (manyFn blankLine) >> blocks blockContext
end

section
open Lean.PrettyPrinter

/--
Parses as `ifVerso` if the option `doc.verso` is `true`, or as `ifNotVerso` otherwise.
-/
public def ifVersoFn (ifVerso ifNotVerso : ParserFn) : ParserFn := fun c s =>
  if c.options.getBool `doc.verso then ifVerso c s
  else ifNotVerso c s

@[inherit_doc ifVersoFn]
public def ifVerso (ifVerso ifNotVerso : Parser) : Parser where
  fn :=
    ifVersoFn ifVerso.fn ifNotVerso.fn

/--
Formatter for `ifVerso`—formats according to the underlying formatters.
-/
@[combinator_formatter ifVerso, expose]
public def ifVerso.formatter (f1 f2 : Formatter) : Formatter := f1 <|> f2

/--
Parenthesizer for `ifVerso`—parenthesizes according to the underlying parenthesizers.
-/
@[combinator_parenthesizer ifVerso, expose]
public def ifVerso.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer := p1 <|> p2

/--
Disables the option `doc.verso` while running a parser.
-/
public def withoutVersoSyntax (p : Parser) : Parser where
  fn :=
    adaptUncacheableContextFn
      (fun c => { c with options := c.options.set `doc.verso false })
      p.fn
  info := p.info

/--
Formatter for `withoutVersoSyntax`—formats according to the underlying formatter.
-/
@[combinator_formatter withoutVersoSyntax, expose]
public def withoutVersoSyntax.formatter (p : Formatter) : Formatter := p
/--
Parenthesizer for `withoutVersoSyntax`—parenthesizes according to the underlying parenthesizer.
-/
@[combinator_parenthesizer withoutVersoSyntax, expose]
public def withoutVersoSyntax.parenthesizer (p : Parenthesizer) : Parenthesizer := p

end

builtin_initialize
  register_parser_alias withoutVersoSyntax
