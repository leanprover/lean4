/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
prelude
public import Lean.DocString.Syntax
import Init.While

set_option linter.missingDocs true

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

/--
A parser that does nothing.
-/
public def skipFn : ParserFn := fun _ s => s

def eatSpaces := takeWhileFn (· == ' ')

def repFn : Nat → ParserFn → ParserFn
  | 0, _ => skipFn
  | n+1, p => p >> repFn n p

/--
Describes a character for an error message. Newline and tab become “newline” and “tab”, while other
characters are quoted.
-/
def describeChar (ch : Char) : String :=
  if ch == '\n' then "newline"
  else if ch == '\t' then "tab"
  else s!"'{ch}'"

/--
Reads one character that satisfies `p`. If the character does not satisfy `p`, the error describes
the unexpected character and mentions `expected` as what would have been read in its place.
-/
def expectFn (p : Char → Bool) (expected : String) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError [expected]
  else if p (c.get' i h) then s.next' c i h
  else s.mkUnexpectedError s!"unexpected {describeChar (c.get' i h)}" [expected]

/--
Reads the character `c` as a token, consuming the whitespace after it when `trailingWs` is set. If
the expected character is not present, the resulting error describes it and gives `c` as what was
expected.
-/
def expectChFn (c : Char) (trailingWs := false) : ParserFn :=
  rawFn (expectFn (· == c) s!"'{c}'") trailingWs

partial def atMostAux (n : Nat) (p : ParserFn) (msg : String) : ParserFn :=
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

def atMostFn (n : Nat) (p : ParserFn) (msg : String) : ParserFn := fun c s =>
  let iniSz  := s.stackSize
  let s := atMostAux n p msg c s
  s.mkNode nullKind iniSz

/--
Whether `c` may appear in the name of a footnote or a link reference. A name is written literally,
so a backslash denotes itself elsewhere and is not part of a name.
-/
-- `closeRefNameWith` describes these characters in the message it reports. If this set changes,
-- make sure to update it as well.
public def isRefNameChar : Char → Bool
  | '[' | ']' | '^' | '\\' | '\n' | '\t' => false
  | _ => true

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

/--
Parses as `p`, but discards the result.
-/
public def ignoreFn (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s' := p c s
  s'.shrinkStack iniSz

/--
Extends the trailing whitespace of the last token in `stx` to `stopPos`, returning the extended
syntax and a flag. The flag is `true` when `stx` contains a token that can be extended. It is
`false` otherwise, and `stx` comes back unchanged.
-/
partial def extendLastTrailing (input : String) (stopPos : String.Pos.Raw) (stx : Syntax) :
    Syntax × Bool :=
  (go stx).run false
where
  /-- The traversal sets the state to `true` when it extends a token, and stops there. -/
  go : Syntax → StateM Bool Syntax
    | .node info k args => do
      let mut args := args
      let mut i := args.size
      while i > 0 do
        i := i - 1
        args ← args.modifyM i go
        if ← get then break
      return .node info k args
    | .atom (.original lead pos trail stop) val => do
      set true
      return .atom (.original lead pos ⟨input, trail.startPos, stopPos⟩ stop) val
    | .ident (.original lead pos trail stop) raw x pre => do
      set true
      return .ident (.original lead pos ⟨input, trail.startPos, stopPos⟩ stop) raw x pre
    | stx => return stx

/--
Runs `ws` and records what it consumes as the trailing whitespace of the most recent token among
the stack elements above `base`. On ordinary parses every token records its own trailing whitespace
as it is parsed, so `wsFallback` consumes nothing. It matters only for error recovery. When the
token that would have recorded the whitespace is lost, `wsFallback` still records the input, so that
the surrounding parse can reprint it.
-/
def wsFallback (ws : ParserFn) (base : Nat) : ParserFn := fun c s =>
  let startPos := s.pos
  let s := ws c s
  if s.hasError || s.pos == startPos then s
  else Id.run do
    -- The most recent token can sit below tokenless elements (an empty optional, a column marker, a
    -- recovery stub). The loop pops elements until one can record the whitespace, and restores them
    -- after. Elements are popped prior to updating them to encourage in-place updates.
    let mut s := s
    let mut saved : Array Syntax := #[]
    while s.stxStack.size > base do
      let top := s.stxStack.back
      s := s.popSyntax
      let (top, extended) := extendLastTrailing c.inputString s.pos top
      if extended then
        s := s.pushSyntax top
        break
      else
        saved := saved.push top
    let mut i := saved.size
    while i > 0 do
      i := i - 1
      s := s.pushSyntax saved[i]!
    return s

/--
Runs `ws` and adds what it consumes to the trailing whitespace of the last token of the element on
top of the stack, so it runs directly after the parser that pushed that element. If that element
contains no token, the input `ws` consumes goes unrecorded and the tree stops covering the source.
-/
def withTrailing (ws : ParserFn) : ParserFn := fun c s =>
  wsFallback ws (s.stxStack.size - 1) c s

/--
Consumes whitespace through the end of the current line and any blank lines that follow.

The first token of the line where content resumes expects to treat that line's indentation as
leading whitespace, so this parser stops before a line with content on it.
-/
def lineTailWs : ParserFn := fun c sStart => Id.run do
  let mut s := sStart
  -- The position after the last newline consumed, where consumption stops. EOI ends the current
  -- line, so this parser also consumes spaces that reach it.
  let mut keep := sStart.pos
  repeat
    let i := s.pos
    if h : c.atEnd i then
      keep := i
      break
    else
      let ch := c.get' i h
      if ch == ' ' then s := s.next' c i h
      else if ch == '\n' then
        s := s.next' c i h
        keep := s.pos
      else break
  return sStart.setPos keep

/--
Extends the leading whitespace of the first token in `stx` back to `startPos`. Syntax without
tokens stays unchanged. A document's first token records the whitespace at its start.
-/
public partial def extendFirstLeading (input : String) (startPos : String.Pos.Raw) (stx : Syntax) :
    Syntax :=
  (go stx).run' false
where
  /-- The traversal sets the state to `true` when it extends a token, and stops there. -/
  go : Syntax → StateM Bool Syntax
    | .node info k args => do
      let mut args := args
      let mut i := 0
      while i < args.size do
        args ← args.modifyM i go
        if ← get then break
        i := i + 1
      return .node info k args
    | .atom (.original lead pos trail stop) val => do
      set true
      return .atom (.original ⟨input, startPos, lead.stopPos⟩ pos trail stop) val
    | .ident (.original lead pos trail stop) raw x pre => do
      set true
      return .ident (.original ⟨input, startPos, lead.stopPos⟩ pos trail stop) raw x pre
    | stx => return stx

/--
Runs `p` and records the input between the starting position and `p`'s first token as that token's
leading whitespace.
-/
def withLeadingHere (p : ParserFn) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError || s.stxStack.size ≤ iniSz then s
  -- In the common case of an unindented block, nothing precedes the first token. The position of
  -- the first pushed element detects this without a traversal.
  else if (s.stxStack.get! iniSz).getPos? == some startPos then s
  else Id.run do
    -- `withLeadingHere` wraps the elements that `p` pushed in one node, so that a single traversal
    -- finds their first token. Taking them off the stack first leaves them uniquely owned, so the
    -- update happens in place.
    let args := s.stxStack.extract iniSz s.stxStack.size
    let mut s := s.shrinkStack iniSz
    let node := extendFirstLeading c.inputString startPos (mkNullNode args)
    for a in node.getArgs do
      s := s.pushSyntax a
    return s

/--
Whether the character before the current position is a newline. Any parser may have consumed that
newline, including the enclosing parser before it invoked this one.
-/
def afterLineEnd (c : ParserContext) (s : ParserState) : Bool :=
  s.pos > 0 && c.get (c.prev s.pos) == '\n'

/--
Whether the most recent token's trailing whitespace ends at the current position and contains a
newline, which means that the token consumed its line's end.
-/
def consumedLineEnd (s : ParserState) : Bool := Id.run do
  let mut i := s.stxStack.size
  while i > 0 do
    i := i - 1
    if let .original _ _ trail _ := (s.stxStack.get! i).getTailInfo then
      return trail.stopPos == s.pos && !trail.all (· != '\n')
  return false

/--
Runs `p` unless the most recent token consumed its line's end as trailing whitespace.
-/
def unlessLineEndConsumed (p : ParserFn) : ParserFn := fun c s =>
  if consumedLineEnd s then s else p c s

/--
If the current position is a newline, consumes it and runs `blanks`. Otherwise consumes nothing.
-/
def optNlWs (blanks : ParserFn := skipFn) : ParserFn := fun c s =>
  if h : c.atEnd s.pos then s
  else if c.get' s.pos h == '\n' then blanks c (s.next' c s.pos h)
  else s

/--
Consumes the rest of the document if it consists only of whitespace. Otherwise, does nothing.
-/
def docEndWs : ParserFn := fun c s =>
  if s.pos < c.endPos &&
      (Substring.Raw.mk c.inputString s.pos c.endPos).all Char.isWhitespace then
    s.setPos c.endPos
  else s

def asTokenAux (trailing : ParserFn) (startPos : String.Pos.Raw) : ParserFn := fun c s =>
  let stopPos  := s.pos
  let leading  := c.mkEmptySubstringAt startPos
  let val      := c.extract startPos stopPos
  -- The token consumes its own trailing whitespace as it is built. If the whitespace parser fails,
  -- `asTokenAux` pushes the token with empty trailing whitespace and keeps the error.
  let s := trailing c s
  let trail :=
    if s.hasError then c.mkEmptySubstringAt stopPos
    else c.substring stopPos s.pos
  s.pushSyntax <| .atom (SourceInfo.original leading startPos trail stopPos) val

/--
Matches an arbitrary parser and pushes the consumed input as a `Syntax.atom`. The `trailing` parser
runs after the token's content, and the input it consumes becomes the token's trailing whitespace.
-/
public def asTokenFn (p : ParserFn) (trailing : ParserFn := skipFn) : ParserFn := fun c s =>
  let startPos := s.pos
  let iniSz := s.stxStack.size
  let s := p c s
  if s.hasError then s
  else asTokenAux trailing startPos c (s.shrinkStack iniSz)

def _root_.Lean.Parser.ParserContext.currentColumn
    (c : ParserContext) (s : ParserState) : Nat :=
  c.fileMap.toPosition s.pos |>.column

def pushColumn : ParserFn := fun c s =>
  let col := c.fileMap.toPosition s.pos |>.column
  s.pushSyntax <| Syntax.mkLit `column (toString col) (SourceInfo.synthetic s.pos s.pos)

def guardColumn (p : Nat → Bool) (message : String) : ParserFn := fun c s =>
  if p (c.currentColumn s) then s else s.mkErrorAt message s.pos

def guardMinColumn (min : Nat) (description : String := s!"expected column at least {min}") : ParserFn :=
  guardColumn (· ≥ min) description

/--
Skips the spaces before the next token and checks its column against `p`, failing with `message`
when `p` rejects it. Consumes nothing, so the token still records that indentation as its leading
whitespace.
-/
def guardColumnFromNextToken (p : Nat → Bool) (message : String) : ParserFn :=
  lookaheadFn (eatSpaces >> guardColumn p message)

def withCurrentColumn (p : Nat → ParserFn) : ParserFn := fun c s =>
  p (c.currentColumn s) c s

/-- Runs `p` with the position at which it starts. -/
def withStartPos (p : String.Pos.Raw → ParserFn) : ParserFn := fun c s => p s.pos c s

/--
An atom containing the input between `startPos` and `stopPos`, at that range, with no leading or
trailing whitespace.
-/
def atomAt (c : ParserContext) (startPos stopPos : String.Pos.Raw) : Syntax :=
  .atom
    (.original (c.mkEmptySubstringAt startPos) startPos (c.mkEmptySubstringAt stopPos) stopPos)
    (c.extract startPos stopPos)

/--
At the end of the input, reports the construct `what` as unterminated. The error points at the
opening delimiter, which runs from `openPos` to `openStop`, and expects those characters again as
the closer. Elsewhere this parser succeeds and consumes nothing.

`nameOpenerLine` adds the line the opener is on to the message.
-/
def unterminatedAtEnd (openPos openStop : String.Pos.Raw) (what : String)
    (nameOpenerLine := false) : ParserFn := fun c s =>
  if c.atEnd s.pos then
    let opener := atomAt c openPos openStop
    let what :=
      if nameOpenerLine then s!"{what} opened on line {(c.fileMap.toPosition openPos).line}"
      else what
    let e :=
      { unexpectedTk := opener, unexpected := s!"unterminated {what}",
        expected := [s!"'{opener.getAtomVal}'"] }
    s.setError e |>.pushSyntax .missing
  else s

/--
At the end of the input, reports the construct `what` as unterminated, naming the line its opening
delimiter is on. That delimiter is `width` characters wide at column `col`, and begins after the
indentation between `openPos`, where the block started, and that column. Elsewhere this parser
succeeds and consumes nothing.
-/
def unterminatedDelimiterAtEnd (openPos : String.Pos.Raw) (col width : Nat) (what : String) :
    ParserFn := fun c s =>
  let indent := col - (c.fileMap.toPosition openPos).column
  unterminatedAtEnd (openPos.offsetBy ⟨indent⟩) (openPos.offsetBy ⟨indent + width⟩) what
    (nameOpenerLine := true) c s

/--
Runs `p` with the column just after the content of the token most recently pushed to the syntax
stack. Trailing whitespace is not part of the token.
-/
def withColumnAfterToken (p : Nat → ParserFn) : ParserFn := fun c s =>
  match s.stxStack.back.getTailPos? with
  | some pos => p (c.fileMap.toPosition pos).column c s
  | none => s.mkError "internal error: expected a token"


/--
Whether a nestable block may open at the current position.

This is the case when the current line contains nothing but spaces and nestable block markers prior to the current position.
-/
def atBlockStart (c : ParserContext) (s : ParserState) : Bool :=
  let position := c.fileMap.toPosition s.pos
  let lineStart := c.fileMap.lineStart position.line
  Id.run do
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

def onlyBlockOpeners : ParserFn := fun c s =>
  if atBlockStart c s then s
  else s.mkErrorAt "beginning of line or sequence of nestable block openers" s.pos

def nl := satisfyFn (· == '\n') "newline"

/--
Reads the end of a line, which is a newline or the end of the input.
-/
def lineEnd : ParserFn := fun c s =>
  if c.atEnd s.pos then s
  else expectFn (· == '\n') "newline" c s

def pushMissing : ParserFn := fun _c s =>
  s.pushSyntax .missing

def strFn (str : String) : ParserFn := asTokenFn <| fun c s =>
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
Ordered lists may have two styles of marker, with trailing dots or parentheses.
-/
public inductive OrderedListType where
   /-- Items like `1.` -/
  | numDot
   /-- Items like `1)` -/
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
  unfold all; intro x; cases x <;> repeat constructor!

/--
Unordered lists may have three markers: asterisks, dashes, or pluses.
-/
public inductive UnorderedListType where
   /-- Items like `*` -/
  | asterisk
   /-- Items like `-` -/
  | dash
   /-- Items like `+` -/
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
  unfold all; intro x; cases x <;> repeat constructor!

def unorderedListMarker (type : UnorderedListType) (trailing : ParserFn := skipFn) :
    ParserFn :=
  nodeFn ``listMarker <| asTokenFn
    (match type with
     | .asterisk => chFn '*'
     | .dash => chFn '-'
     | .plus => chFn '+')
    trailing

def orderedListMarker (type : OrderedListType) (trailing : ParserFn := skipFn) : ParserFn :=
  nodeFn ``listMarker <| asTokenFn
    (takeWhile1Fn (·.isDigit) "digits" >>
     match type with
     | .numDot => chFn '.'
     | .parenAfter => chFn ')')
    trailing

def unorderedMarkersFn := atomicFn (go UnorderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (unorderedListMarker x)
    | x :: xs => atomicFn (unorderedListMarker x) <|> go xs

def numberingFn := atomicFn (go OrderedListType.all)
where
  go
    | [] => fun _ s => s.mkError "no list type"
    | [x] => atomicFn (orderedListMarker x)
    | x :: xs => atomicFn (orderedListMarker x) <|> go xs

/--
Parses a character that's allowed as part of inline text. This resolves escaped characters and
performs limited lookahead for characters that only begin a different inline as part of a sequence.
-/
public def inlineTextCharFn : ParserFn := fun c s =>
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
    | '\n' => s.mkUnexpectedErrorAt "unexpected newline" i
    | '*' | '_' | '[' | ']' | '{' | '}' | '`' =>
      (s.setPos i).mkUnexpectedError s!"unexpected '{curr}' (use '\\{curr}' to escape)" ["text"]
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

/--
Parses block opener prefixes. If this parser succeeds at the beginning of a line, then a special
block is beginning.
-/
public def blockOpenerFn := atomicFn <|
  eatSpaces >>
  (atomicFn ((unorderedMarkersFn >> chFn ' ')) <|> -- Unordered list
   atomicFn ((numberingFn >> chFn ' ')) <|> -- Ordered list
   atomicFn (strFn ": ") <|> -- Description list item
   atomicFn (atLeastFn 3 (chFn ':')) <|> -- Directive
   atomicFn (atLeastFn 3 (chFn '`')) <|> -- Code block
   atomicFn (strFn "%%%") <|> -- Metadata
   atomicFn (chFn '>')) -- Block quote

/--
Whether the line after the newline at the current position continues a paragraph. It continues when
the line begins with content other than a block opener.

If the current position is not a newline, returns `false`.
-/
def lineContinues (c : ParserContext) (s : ParserState) : Bool := Id.run do
  let mut s := s
  let i := s.pos
  if h : c.atEnd i then return false
  else if c.get' i h != '\n' then return false
  else s := s.next' c i h
  repeat
    let i := s.pos
    if h : c.atEnd i then return true
    else if c.get' i h == ' ' then s := s.next' c i h
    else if c.get' i h == '\n' then return false
    else break
  return (blockOpenerFn c s).hasError

/--
The trailing whitespace of a token that may end a block's inline content, which belongs to a
paragraph, a header, a description list's term, or a footnote definition.

At a newline, the content carries on to the next line when `allowNewlines` is set and that line
begins content other than a block opener. This parser then consumes nothing, and a line break inline
token consumes the newline. Otherwise, the content ends here, and `blockTailWs` consumes the newline
and the blank lines after it, up to and including the last newline. If the current position is not a
newline, it does nothing.
-/
def blockTailWs (allowNewlines : Bool) : ParserFn := fun c s =>
  if h : c.atEnd s.pos then s
  else if c.get' s.pos h != '\n' then s
  else if allowNewlines && lineContinues c s then s
  else lineTailWs c s

/--
Parses an argument value, which may be a string, an identifier, or a numeral. The value's token
records the input consumed by `trailing` as its trailing whitespace.
-/
public def valFn (trailing : ParserFn := skipFn) : ParserFn := fun c s =>
  if h : c.atEnd s.pos then
    s.mkEOIError
  else
    let ch := c.get' s.pos h
    let i := s.stackSize
    let finish (s : ParserState) : ParserState :=
      if s.hasError then s else withTrailing trailing c s
    if ch == '\"' then
      let s := finish (strLitFnAux s.pos false c (s.next' c s.pos h))
      s.mkNode ``ArgVal.str i
    else if isIdFirst ch || isIdBeginEscape ch then
      let s := finish (rawIdentFn (includeWhitespace := false) c s)
      s.mkNode ``ArgVal.ident i
    else if ch.isDigit then
      let s := finish (numberFnAux false c s)
      s.mkNode ``ArgVal.num i
    else
      s.mkError "identifier, string, or number"

def withCurrentStackSize (p : Nat → ParserFn) : ParserFn := fun c s =>
  p s.stxStack.size c s

/-- Matches the character indicated, pushing nothing to the stack in case of success -/
def skipChFn (c : Char) : ParserFn :=
  expectFn (· == c) s!"'{c}'"

def skipToNewline : ParserFn :=
    takeUntilFn (· == '\n')

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

/--
Recovers from a parse error by skipping input until one or more complete blank lines has been
skipped.
-/
public def recoverBlock (p : ParserFn) (final : ParserFn := skipFn) : ParserFn :=
  recoverFn p fun _ =>
    ignoreFn skipBlock >> final

/--
Runs `p`, and on failure consumes input with `recover` until parsing may continue. The error is
recorded where `p` stopped, so that it marks the input that could not be read rather than the input
that recovery passed over.
-/
def recoverAtErrPos (p recover : ParserFn) : ParserFn := fun c s =>
  let s := p c s
  if let some msg := s.errorMsg then
    let errPos := s.pos
    let s' := recover c { s with errorMsg := none }
    if s'.hasError then s
    else { s with
      pos := s'.pos,
      errorMsg := none,
      stxStack := s'.stxStack,
      recoveredErrors := s.recoveredErrors.push (errPos, s'.stxStack, msg)
    }
  else s

@[inherit_doc recoverAtErrPos]
def recoverBlockAtErrPos (p : ParserFn) : ParserFn := recoverAtErrPos p (ignoreFn skipBlock)

/--
Recovers from a parse error in a role by reading to its closing brace and consuming it. If the line
has no brace, recovery skips the block.
-/
def recoverRoleAtErrPos (p : ParserFn) : ParserFn :=
  recoverAtErrPos p <|
    -- The brace is the role's closing delimiter, so recovery pushes it.
    atomicFn (ignoreFn (takeUntilFn (fun c => c == '}' || c == '\n')) >> chFn '}') <|>
    ignoreFn skipBlock

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

def recoverEol (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => ignoreFn <| skipToNewline

@[inherit_doc recoverAtErrPos]
def recoverEolAtErrPos (p : ParserFn) : ParserFn := recoverAtErrPos p (ignoreFn skipToNewline)

@[inherit_doc recoverAtErrPos]
def recoverLineAtErrPos (p : ParserFn) : ParserFn := recoverAtErrPos p (ignoreFn skipRestOfLine)

/--
Closes a name with `closer`. If name parsing stopped at a non-name character, the error message is
informative. A name ends at `]` and may not span a line, so those expect `closer` instead.
-/
def closeRefNameWith (closer : String) : ParserFn := fun c s =>
  let cutShort :=
    if h : c.atEnd s.pos then false
    else
      let ch := c.get' s.pos h
      !(ch == ']' || ch == '\n')
  -- The characters listed are those `isRefNameChar` rejects, less the two that end a name.
  if cutShort then s.mkError "a character other than '^', '[', '\\', or a tab"
  else strFn closer c s

@[inherit_doc closeRefNameWith]
def closeRefName : ParserFn := closeRefNameWith "]"

@[inherit_doc recoverAtErrPos]
def recoverWsAtErrPos (p : ParserFn) : ParserFn :=
  recoverAtErrPos p (ignoreFn <| takeUntilFn (fun c => c == ' ' || c == '\n'))

/--
Recovery inside an argument list reads to the next whitespace, or to a character that closes the
list or the argument, so that the closer is still there for the parser that waits for it.
-/
def recoverArgAtErrPos (closes : Char → Bool) (p : ParserFn) : ParserFn :=
  recoverAtErrPos p (ignoreFn <| takeUntilFn (fun c => c == ' ' || c == '\n' || closes c))

/--
Runs `p`. On failure, skips to the end of the line and replaces everything `p` pushed with `stxs`,
so that an enclosing node of fixed arity still receives children. The error is recorded where `p`
stopped.
-/
def recoverEolWithAtErrPos (stxs : Array Syntax) (p : ParserFn) : ParserFn := fun c s =>
  let iniSz := s.stxStack.size
  let s := p c s
  if let some msg := s.errorMsg then
    let errPos := s.pos
    let s' := (ignoreFn skipToNewline) c {s with errorMsg := none}
    if s'.hasError then s
    else
      let s' := stxs.foldl (init := s'.shrinkStack iniSz) (·.pushSyntax ·)
      { s' with recoveredErrors := s.recoveredErrors.push (errPos, s'.stxStack, msg) }
  else s

def recoverSkip (p : ParserFn) : ParserFn :=
  recoverFn p fun _ => skipFn

/-- Recovers from an error by pushing the provided syntax items, without adjusting the position. -/
def recoverHereWith (stxs : Array Syntax) (p : ParserFn) : ParserFn :=
  recoverFn p fun rctx =>
    show ParserFn from
      fun _ s => stxs.foldl (init := s.restore rctx.initialSize rctx.initialPos) (·.pushSyntax ·)

/--
The whitespace after an argument, recorded on the argument's last token as its trailing whitespace.

Without `multiline` this is the spaces that follow. With `multiline` it also takes the line ending
and any blank lines, up to and including the last newline, but only when the next line is indented
to at least the given column, which is what continues the argument list. The next argument's first
token records that indentation as its leading whitespace. A line indented less ends the list, and
this consumes nothing.
-/
public def argEndWs : (multiline : Option Nat) → ParserFn
  | none => eatSpaces
  | some n => fun c s =>
    let s1 := lineTailWs c s
    if s1.pos == s.pos then s
    else if c.currentColumn (eatSpaces c s1) ≥ n then s1
    else s

/--
Parses an argument to a role, directive, command, or code block, which may be named or positional or
a flag. The argument's final token records the input `tail` consumes as its trailing whitespace.

Error recovery stops at characters that satisfy `closes`, which should delimit the current argument
list (e.g. via a role's `}`).
-/
public def argFn (tail : ParserFn := skipFn) (closes : Char → Bool := fun _ => false) :
    ParserFn :=
    withCurrentStackSize fun iniSz =>
      flag <|> withParens iniSz <|> potentiallyNamed iniSz <|> (valFn tail >> mkAnon iniSz)
where
  mkNamed (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Arg.named iniSz
  mkNamedNoParen (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Arg.named_no_paren iniSz
  mkAnon (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``Arg.anon iniSz
  mkIdent (iniSz : Nat) : ParserFn := fun _ s => s.mkNode ``ArgVal.ident iniSz
  flag : ParserFn :=
    (nodeFn ``Arg.flag_on
      (asTokenFn (strFn  "+") >> recoverNonSpace noSpace >>
      recoverWs (rawIdentFn (includeWhitespace := false))) <|>
    nodeFn ``Arg.flag_off
      (asTokenFn (strFn "-") >> recoverNonSpace noSpace >>
      recoverWs (rawIdentFn (includeWhitespace := false)))) >>
    withTrailing tail
  noSpace : ParserFn := fun c s =>
    if h : c.atEnd s.pos then s
    else
      let ch := c.get' s.pos h
      if ch == ' ' then
        s.mkError "no space before"
      else s
  potentiallyNamed iniSz :=
      atomicFn (rawIdentFn (includeWhitespace := false)) >> withTrailing eatSpaces >>
       ((atomicFn (asTokenFn (strFn ":=") eatSpaces) >>
         valFn (eatSpaces >> tail) >> mkNamedNoParen iniSz) <|>
        (mkIdent iniSz >> mkAnon iniSz >> withTrailing tail))
  -- A recoverable token step consumes and records its whitespace even when the token is lost.
  -- `wsFallback` runs after the recovery too, and records the whitespace on the most recent
  -- surviving token, past the recovery's stub.
  recovering (closes : Char → Bool) (iniSz : Nat) (p : ParserFn) : ParserFn :=
    recoverArgAtErrPos closes p >> wsFallback eatSpaces iniSz
  withParens iniSz :=
    -- Inside the parentheses, the `)` closes the argument as well.
    let inParens := fun c => c == ')' || closes c
    atomicFn (asTokenFn (strFn "(") eatSpaces) >>
    recovering inParens iniSz (rawIdentFn (includeWhitespace := false)) >>
    recovering inParens iniSz (asTokenFn (strFn ":=")) >>
    recovering inParens iniSz valFn >>
    recoverEol (asTokenFn (strFn ")")) >> wsFallback (eatSpaces >> tail) iniSz >>
    mkNamed iniSz

/--
Fails when the previous character is a newline.
-/
def guardSameLine : ParserFn := fun c s =>
  if afterLineEnd c s then s.mkError "argument on the same line" else s

/--
Skips whitespace between a name and its arguments. When the argument is `none`, the context is a
single line and the whitespace may only be the space character. When it is `some N`, newlines are
allowed and `N` is the minimum indentation column. The tokens themselves consume this whitespace as
they are parsed, so on ordinary parses this parser consumes nothing. Call sites wrap it in
`wsFallback`, so that it still records input consumed during error recovery.
-/
def nameArgWhitespace : (multiline : Option Nat) → ParserFn
  -- After a line end, the construct that resumes on the next line records its indentation, not
  -- this argument list.
  | none => fun c s => if afterLineEnd c s then s else eatSpaces c s
  | some n => fun c s =>
    let s1 := lineTailWs c s
    let s' := eatSpaces c s1
    if c.currentColumn s' ≥ n then s1
    else s'.mkErrorAt s!"column at least {n}" s'.pos

/--
Runs `p` and records the indentation before it as the leading whitespace of `p`'s first token. A
multiline argument's indentation belongs there.
-/
def withArgIndent : (multiline : Option Nat) → ParserFn → ParserFn
  | none, p => p
  | some _, p => withLeadingHere (eatSpaces >> p)

/--
Parses zero or more arguments to a role, directive, command, or code block. Each argument's final
token records the input `tail` consumes as its trailing whitespace. A single-line argument list must
stand on the line the parser starts on. A starting position at the beginning of a line means the
list has already ended, so the list is empty.

Error recovery stops at characters that satisfy `closes`, which should delimit the current argument
list (e.g. via a role's `}`).
-/
public def argsFn (multiline : Option Nat := none) (tail : ParserFn := argEndWs multiline)
    (closes : Char → Bool := fun _ => false) : ParserFn := fun c s =>
  let base := s.stxStack.size
  match multiline with
  | none =>
    sepByFn true (guardSameLine >> argFn tail closes) (guardSameLine >> wsFallback eatSpaces base)
      c s
  | some n =>
    -- After an argument's tail consumed the line end, the argument parser already validated the
    -- next line's indentation, so the separator has nothing to check or consume.
    sepByFn true (withArgIndent (some n) (argFn tail closes))
      (unlessLineEndConsumed (wsFallback (nameArgWhitespace (some n)) base)) c s

/--
Replaces any error from `p` at the initial position with `expected msg`. This ensures that
each sub-parser of `delimitedInline` contributes a clear expected-token name, and clears
unhelpful generic "unexpected" messages from inner parsers so that the more informative message
from `inlineTextChar` survives error merging via `<|>`.
-/
def expectedFn (msg : String) (p : ParserFn) : ParserFn := fun c s =>
  let iniPos := s.pos
  let s := p c s
  if s.hasError && s.pos == iniPos then
    s.setError { expected := [msg] }
  else s

/--
Reads the name of a footnote or link reference, which is a run of the characters that a name may
contain. `description` names what was expected where the name begins.
-/
def refNameFn (description : String) : ParserFn :=
  expectedFn description (many1Fn (satisfyFn isRefNameChar description))

/--
Parses a name and zero or more arguments to a role, directive, command, or code block. The final
token of the name and of each argument records the input that `tail` consumes as its trailing
whitespace. In a single-line context, the name and arguments must stand on the line the parser
starts on. A starting position at the beginning of a line fails to parse a name.

The caller's own tokens record the whitespace before the name. If a caller lets this parser consume
that whitespace instead, no token records it.

Error recovery stops at characters that satisfy `closes`, which should delimit the current argument
list (e.g. via a role's `}`).
-/
public def nameAndArgsFn (multiline : Option Nat := none) (tail : ParserFn := argEndWs multiline)
    (closes : Char → Bool := fun _ => false) : ParserFn := fun c s =>
  let base := s.stxStack.size
  (nameArgWhitespace multiline >>
   (if multiline.isNone then guardSameLine else skipFn) >>
   withArgIndent multiline (expectedFn "identifier" (rawIdentFn (includeWhitespace := false))) >>
   withTrailing tail >> wsFallback (nameArgWhitespace multiline) base >>
   argsFn (multiline := multiline) (tail := tail) (closes := closes)) c s

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
  /--
  The trailing whitespace parser for the final token of a top-level inline element.
  -/
  tail : ParserFn := skipFn
deriving Inhabited

/- Parsing inlines:
 * Inline parsers may not consume trailing whitespace, and must be robust in the face of leading whitespace
-/

/--
A linebreak that isn't a block break (that is, there's non-space content on the next line)
-/
def linebreakFn (ctxt : InlineCtxt) : ParserFn :=
  if ctxt.allowNewlines then
    nodeFn ``Inline.linebreak <| asTokenFn fun c s =>
      if lineContinues c s then skipChFn '\n' c s
      else s.mkError "newline"
  else
    errorFn "Newlines not allowed here"

partial def notInLink (ctxt : InlineCtxt) : ParserFn := fun _ s =>
  if ctxt.inLink then s.mkUnexpectedError "a link inside a link" else s

/-- The context for inline elements nested inside another inline element. -/
def InlineCtxt.inner (ctxt : InlineCtxt) : InlineCtxt := { ctxt with tail := skipFn }

-- Like `satisfyFn (· == '\n')` but with a better error message that mentions what was expected.
def newlineOrUnexpected (msg : String) : ParserFn := fun c s =>
  let i := s.pos
  if h : c.atEnd i then s.mkEOIError
  else if c.get' i h == '\n' then s.next' c i h
  else s.mkUnexpectedError s!"unexpected {describeChar (c.get' i h)}" [msg]

mutual
  partial def emphLike
    (name delimKind : SyntaxNodeKind) (char : Char) (what plural noun : String)
    (getter : InlineCtxt → Option Nat) (setter : InlineCtxt → Option Nat → InlineCtxt)
    (ctxt : InlineCtxt) : ParserFn :=
    nodeFn name <|
    withStartPos fun openPos =>
    withCurrentColumn fun c =>
      atomicFn (nodeFn delimKind <| asTokenFn (asTokenFn (opener ctxt) >> notFollowedByFn (chFn ' ' false <|> chFn '\n' false) "space or newline after opener")) >>
      (recoverSkip <|
        withCurrentColumn fun c' =>
          let count := c' - c
          manyFn (inlineFn ((setter ctxt (some count)).inner)) >>
          unterminatedAtEnd openPos (openPos.offsetBy ⟨count⟩) noun >>
          nodeFn delimKind (asTokenFn (atomicFn (noSpaceBefore >>
            repFn count (expectFn (· == char) s!"'{tok count}' to close {noun}"))) ctxt.tail))

  where
    tok (count : Nat) : String := String.ofList (List.replicate count char)
    opener (ctxt : InlineCtxt) : ParserFn :=
      match getter ctxt with
      | none => many1Fn (expectFn (· == char) s!"{plural} to open {noun}")
      | some 1 | some 0 => fun _ s => s.mkUnexpectedError s!"no room left to {what} here"
      -- A nested opener is a run of at least one delimiter that is shorter than the delimiter it is
      -- nested in, so that the close of the outer element remains unambiguous.
      | some d =>
        expectFn (· == char) s!"'{char}' to open nested {noun}" >>
        atMostFn (d - 2) (satisfyFn (· == char) s!"{char}") s!"at most {d - 1} {plural}"
    noSpaceBefore : ParserFn := fun c s =>
      if s.pos == 0 then s
      else
        let prior := c.get (c.prev s.pos)
        if prior.isWhitespace then
          s.mkUnexpectedError s!"unexpected space before the closing '{char}'"
        else s

  /--
  Parses emphasis: a matched pair of one or more `_`.
  -/
  public partial def emphFn :=
    emphLike ``Inline.emph ``emphDelimiter '_' "emphasize" "underscores" "emphasis" (·.emphDepth) ({· with emphDepth := ·})

  /--
  Parses bold: a matched pair of one or more `*`.
  -/
  public partial def boldFn :=
    emphLike ``Inline.bold ``boldDelimiter '*' "bold" "asterisks" "bold text" (·.boldDepth) ({· with boldDepth := ·})

  /--
  Parses inline code. The closing delimiter records the input `tail` consumes as its trailing
  whitespace.
  -/
  public partial def codeFn (tail : ParserFn := skipFn) : ParserFn :=
    nodeFn ``Inline.code <|
    withStartPos fun openPos =>
    withCurrentColumn fun c =>
      atomicFn opener >>
      ( atomicFn <|
        withCurrentColumn fun c' =>
          let count := c' - c
          recoverCode <|
            nodeFn versoCodeKind
              (asTokenFn (many1Fn <| codeContentsFn (count - 1))) >>
            unterminatedAtEnd openPos (openPos.offsetBy ⟨count⟩) "inline code" >>
            closer count)
  where
    opener : ParserFn :=
      nodeFn ``codeDelimiter <|
        asTokenFn (many1Fn (expectFn (· == '`') "backticks to open inline code"))
    closer (count : Nat) : ParserFn :=
      nodeFn ``codeDelimiter (asTokenFn
        (atomicFn (repFn count
          (expectFn (· == '`') s!"'{String.ofList (.replicate count '`')}' to close inline code")) >>
         notFollowedByFn (satisfyFn (· == '`') "`") "backtick")
        tail)
    recoverCode (p : ParserFn) : ParserFn :=
      recoverFn p fun rctx =>
        (show ParserFn from fun _ s => s.restore rctx.initialSize rctx.initialPos) >>
        atomicFn (nodeFn versoCodeKind
          (asTokenFn (takeWhileFn (· ≠ '\n')) (ignoreFn (chFn '\n' <|> eoiFn))) >>
          pushMissing)
    codeContentsFn (maxCount : Nat) : ParserFn :=
      atomicFn (asTokenFn (satisfyFn (maxCount > 0 && · == '`') >> atMostFn (maxCount - 1) (chFn '`') s!"at most {maxCount} backticks")) <|>
      expectFn (· != '`') "a character other than a backtick"

  /--
  Parses mathematics.
  -/
  public partial def mathFn (tail : ParserFn := skipFn) : ParserFn :=
    atomicFn (nodeFn ``Inline.display_math <| nodeFn ``displayMathMarker (strFn "$$") >> codeFn tail) <|>
    atomicFn (nodeFn ``Inline.inline_math <| nodeFn ``inlineMathMarker (strFn "$") >> codeFn tail)

  /-- Reads a prefix of a line of text, stopping at a text-mode special character. -/
  public partial def textFn (ctxt : InlineCtxt := {}) : ParserFn :=
    nodeFn ``Inline.text <|
      nodeFn versoTextKind <|
        asTokenFn (many1Fn inlineTextCharFn) ctxt.tail

  /-- Parses a link. -/
  public partial def linkFn (ctxt : InlineCtxt) :=
    nodeFn ``Inline.link <|
      (atomicFn (notInLink ctxt >> strFn "[" >> notFollowedByFn (chFn '^') "'^'" )) >>
      (recoverEol <|
        many1Fn (inlineFn {ctxt.inner with inLink := true}) >>
        strFn "]" >> linkTargetFn ctxt.tail)

  /-- Parses a footnote. -/
  public partial def footnoteFn (ctxt : InlineCtxt) :=
    nodeFn ``Inline.footnote <|
      (atomicFn (notInLink ctxt >> strFn "[^" )) >>
      (recoverLineAtErrPos <|
        nodeFn versoRefKind (asTokenFn (refNameFn "a footnote name")) >>
        closeRefName >> withTrailing ctxt.tail)

  partial def linkTargetFn (tail : ParserFn := skipFn) : ParserFn := fun c s =>
    let s := (ref <|> url) c s
    if s.hasError then
      match s.errorMsg with
      | some e => s.setError { e with
          expected := ["link target '(url)' or '[ref]' (use '\\[' for a literal '[')"] }
      | none => s
    else s
  where
    notUrlEnd := expectedFn "URL" (satisfyEscFn (· ∉ ")\n".toList)) >> takeUntilEscFn (· ∈ ")\n".toList)
    notRefEnd := refNameFn "a reference name"
    ref : ParserFn :=
      nodeFn ``LinkTarget.ref <|
        (atomicFn <| strFn "[") >>
        recoverEolAtErrPos (nodeFn versoRefKind (asTokenFn notRefEnd) >> closeRefName >>
          withTrailing tail)
    url : ParserFn :=
      nodeFn ``LinkTarget.url <|
        (atomicFn <| strFn "(") >>
        recoverEolAtErrPos
          (nodeFn versoLinkUrlKind (asTokenFn notUrlEnd) >> strFn ")" >> withTrailing tail)

  /-- Parses an image. -/
  public partial def imageFn (tail : ParserFn := skipFn) : ParserFn :=
    nodeFn ``Inline.image <|
      atomicFn (strFn "![") >>
      (recoverSkip <|
        nodeFn versoImageAltKind (asTokenFn (takeUntilEscFn (· ∈ "]\n".toList))) >>
        strFn "]" >>
        linkTargetFn tail)

  /-- Parses a role. -/
  public partial def roleFn (ctxt : InlineCtxt) : ParserFn :=
    nodeFn ``Inline.role <| withCurrentStackSize fun base =>
      intro base >> (bracketed <|> atomicFn nonBracketed)
  where
    intro (base : Nat) :=
      atomicFn (chFn '{') >> recoverRoleAtErrPos (withTrailing eatSpaces >>
      nameAndArgsFn (tail := argEndWs none) (closes := (· == '}')) >>
      wsFallback eatSpaces base >>
      rawFn (fun c s =>
        let i := s.pos
        if h : c.atEnd i then s.mkEOIError [closeMsg]
        else if c.get' i h == '}' then s.next' c i h
        else (s.setPos i).mkUnexpectedError s!"unexpected {describeChar (c.get' i h)}" [closeMsg])
          false)
    closeMsg := "positional argument, named argument, flag, or '}' (use '\\{' for a literal '{')"
    bracketed :=
      atomicFn (nodeFn nullKind (expectChFn '[')) >>
      recoverBlock (manyFn (inlineFn ctxt.inner) >>
        nodeFn nullKind (expectChFn ']' >> withTrailing ctxt.tail))
    nonBracketed : ParserFn := fun c s =>
      let s := s.pushSyntax (mkNullNode #[])
      let s := nodeFn nullKind (delimitedInlineFn ctxt) c s
      s.pushSyntax (mkNullNode #[])

  /--
  Parses an inline that is self-delimiting (that is, with well-defined start and stop characters).
  -/
  public partial def delimitedInlineFn (ctxt : InlineCtxt) : ParserFn :=
    expectedFn "'_'" (emphFn ctxt) <|> expectedFn "'*'" (boldFn ctxt) <|>
    expectedFn "'`'" (codeFn ctxt.tail) <|> mathFn ctxt.tail <|>
    expectedFn "'{'" (roleFn ctxt) <|> imageFn ctxt.tail <|>
    linkFn ctxt <|> footnoteFn ctxt

  /--
  Parses any inline element.
  -/
  public partial def inlineFn (ctxt : InlineCtxt) : ParserFn :=
    textFn ctxt <|> expectedFn "newline" (linebreakFn ctxt) <|> delimitedInlineFn ctxt
end

/--
Parses a line of text (that is, one or more inline elements). When `recordTrailing` is set, each
top-level inline's final token consumes the whitespace that follows it as its trailing whitespace.
-/
def textLineFn (allowNewlines := true) (recordTrailing := false) : ParserFn :=
  if !recordTrailing then
    many1Fn (inlineFn { allowNewlines })
  else fun c s => Id.run do
    let ctxt : InlineCtxt := { allowNewlines, tail := blockTailWs allowNewlines }
    let iniSz := s.stxStack.size
    let mut s := s
    let mut first := true
    repeat
      let itSz := s.stxStack.size
      let itPos := s.pos
      let itRec := s.recoveredErrors.size
      s := inlineFn ctxt c s
      if s.hasError then
        if s.pos == itPos && !first then
          s := s.restore itSz itPos
        break
      if s.pos == itPos then
        s := s.mkUnexpectedError "invalid 'many' parser combinator application, parser did not consume anything"
        break
      first := false
      -- After an inline that parsed without error recovery, its final token's trailing parser made
      -- the line-end decision. Stopping at a newline means the next line continues. A token that
      -- consumed its line's end as trailing whitespace ends the text. After error recovery no token
      -- made the decision, so the next round parses a linebreak by lookahead as usual.
      if s.recoveredErrors.size == itRec then
        if h : c.atEnd s.pos then
          break
        else if c.get' s.pos h == '\n' then
          if allowNewlines then
            s := nodeFn ``Inline.linebreak (asTokenFn (skipChFn '\n')) c s
          else
            break
        else if consumedLineEnd s then
          break
    return s.mkNode nullKind iniSz

open Lean.Parser.Term in
/-- A non-`meta` copy of `Lean.Doc.Syntax.metadataContents`. -/
@[run_builtin_parser_attribute_hooks]
public def metadataContents : Parser :=
  structInstFields (sepByIndent structInstField ", " (allowTrailingSep := true))

def withPercents : ParserFn → ParserFn := fun p =>
  adaptUncacheableContextFn (fun c => {c with tokens := c.tokens.insert "%%%" "%%%"}) p

/--
Records that the parser is presently parsing a list.
-/
public structure InList where
  /-- The indentation of list markers. -/
  indentation : Nat
  /-- The specific list type and its marker style -/
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
  Whether blocks in this context are at the document's top level, rather than the contents of
  another block.
  -/
  topLevel : Bool := true
  /--
  Whether each block's final token records the whitespace that follows the block as its trailing
  whitespace.
  -/
  recordTrailing : Bool := false
  /--
  The block's maximal directive size (that is, the greatest number of allowed colons).
  -/
  maxDirective : Option Nat := none
  /--
  The nested list context, innermost first.
  -/
  inLists : List InList := []
  /--
  The position at which the document content starts, used to allow headers on the first line of a
  docstring (e.g. `/-! # Header -/`). With the default value `⟨1, 0⟩`, the beginning-of-line check
  is unaffected for normal documents.
  -/
  docStartPosition : Position := ⟨1, 0⟩
  /--
  The base column of the docstring, which is the least indentation of any non-empty line in it,
  including the opening and closing delimiters. For indented docstrings (e.g. inside `where`
  blocks), beginning-of-line checks use this column instead of requiring column 0. With the default
  value 0, the check is equivalent to `column == 0`.
  -/
  baseColumn : Nat := 0
deriving Inhabited, Repr

/--
The trailing whitespace of a block's final token. When `recordTrailing` is set, the token takes the
rest of its line and any blank lines that follow. Otherwise it takes nothing.
-/
def blockTrailingWs (ctxt : BlockCtxt) : ParserFn :=
  if ctxt.recordTrailing then lineTailWs else skipFn

/--
The separator between blocks in a sequence.
-/
def blockSepFallback (base : Nat) : ParserFn := fun c s =>
  if s.recoveredErrors.isEmpty then s
  else wsFallback lineTailWs base c s

/--
Finds the minimum column of the first non-whitespace character on each non-empty content line
between `startPos` and `endPos`, returning `init` if no such line exists.
-/
def minContentIndent (text : FileMap) (startPos endPos : String.Pos.Raw)
    (init : Nat) : Nat := Id.run do
  let mut result := init
  let mut thisLineCol := 0
  if h : endPos ≤ text.source.rawEndPos then
    let endPos := text.source.posGE endPos h
    if h : startPos ≤ text.source.rawEndPos then
      let mut i := text.source.posGE startPos h
      let mut afterNewline := false
      while h : i ≠ text.source.endPos do
        let c := i.get h
        i := i.next h
        if i > endPos then break
        if c == '\n' then
          afterNewline := true
          thisLineCol := 0
        else if afterNewline && c != ' ' then
          result := min result thisLineCol
          afterNewline := false
        else thisLineCol:= thisLineCol + 1
  return result

/--
Computes the `BlockCtxt` for parsing a docstring that starts at `startPos` in the given file map.
`endPos` is the position of the `-` in the closing delimiter. When the docstring content starts
mid-line (e.g. `/-! # Header -/`), the `docStartPosition` is set to the position after any leading
spaces so that headers on the first line are recognized. For indented docstrings, `baseColumn` is
computed as the minimum column among the opening delimiter, closing delimiter, and the least-indented
non-empty content line.
-/
public def BlockCtxt.forDocString (text : FileMap)
    (startPos : String.Pos.Raw) (endPos : String.Pos.Raw) : BlockCtxt :=
  -- Compute baseColumn from the opening `/--` or `/-!` delimiter, the closing `-/` delimiter,
  -- and the least-indented non-empty content line.
  -- `startPos` points to just after `/--`, so subtract 3 to get the column of `/`.
  -- Both `/--` and `/-!` are 3 ASCII bytes.
  let openCol := (text.toPosition (startPos.decreaseBy 3)).column
  let closeCol := (text.toPosition endPos).column
  let baseColumn := min openCol closeCol
  -- Scan content lines to find the minimum indentation of any non-empty line.
  -- We look for non-whitespace characters that appear after a newline and check their column.
  let baseColumn := minContentIndent text startPos endPos baseColumn
  let position := text.toPosition startPos
  if position.column ≤ baseColumn then { baseColumn }
  else
    -- Skip leading spaces to find where content actually starts
    let pos := Id.run do
      if h : startPos ≤ text.source.rawEndPos then
        let mut pos := text.source.posGE startPos h
        while h : pos ≠ text.source.endPos do
          if pos.get h == ' ' then
            pos := pos.next h
          else
            break
        return pos.offset
      else text.source.rawEndPos
    { docStartPosition := text.toPosition pos, baseColumn }

/--
Whether a block may open at the current position: at the start of a line, or on the docstring's
first line, where the opening delimiter precedes the content.
-/
def atBol (ctxt : BlockCtxt) (c : ParserContext) (s : ParserState) : Bool :=
  let pos := c.fileMap.toPosition s.pos
  pos.column ≤ ctxt.baseColumn ||
  (pos.line == ctxt.docStartPosition.line && pos.column ≤ ctxt.docStartPosition.column)

def bol (ctxt : BlockCtxt) : ParserFn := fun c s =>
  if atBol ctxt c s then s
  else s.mkErrorAt s!"beginning of line at {c.fileMap.toPosition s.pos}" s.pos

def bolThen (ctxt : BlockCtxt) (p : ParserFn) (description : String) : ParserFn := fun c s =>
  if atBol ctxt c s then
    let s := p c s
    if s.hasError then
      s.mkErrorAt description s.pos
    else s
  else s.mkErrorAt description s.pos

open Lean.Parser.Term in
/--
Parses a metadata block, which contains the contents of a Lean structure initialization but is
surrounded by `%%%` on each side.
-/
public def metadataBlockFn (ctxt : BlockCtxt := {}) : ParserFn :=
  nodeFn ``Block.metadata_block <|
    atLineStart >>
    atTopLevel >>
    opener >>
    withPercents metadataContents.fn >>
    closer
where
  -- In a position where the block can't open, reading the opening delimiter commits the parse to a
  -- message that names the construct. The unexpected token that's used includes the source range
  -- for the message.
  atLineStart : ParserFn := fun c s =>
    if atBol ctxt c s then s
    else
      let s' := atomicFn (eatSpaces >> strFn "%%%") c s
      if s'.hasError then s'
      else s'.setError { unexpectedTk := s'.stxStack.back, unexpected := misplacedMsg }
  misplacedMsg := "unexpected metadata block opener '%%%' (must be at start of line)"
  -- A metadata block describes the document or a section of it, so one written inside another
  -- block ends that block and attaches at the top level. The contents of a directive cannot end
  -- this way. Inside a directive the parser therefore consumes the `%%%` before it reports the
  -- failure, which commits the parse to the error.
  atTopLevel : ParserFn := fun c s =>
    if ctxt.topLevel then s
    else if ctxt.maxDirective.isSome then
      let s := atomicFn (bolThen ctxt (eatSpaces >> strFn "%%%") "%%% (at line beginning)") c s
      if s.hasError then s else s.mkUnexpectedError nestedMsg
    else s.mkUnexpectedError nestedMsg
  nestedMsg := "metadata blocks may only appear at the document's top level"
  opener :=
    atomicFn (bolThen ctxt (eatSpaces >> strFn "%%%") "%%% (at line beginning)") >>
    -- The opener records the indentation before the contents, so the Lean parser that reads them
    -- starts at their column and aligns the fields there. That column must be the base column.
    withTrailing (eatSpaces >> ignoreFn (chFn '\n') >> eatSpaces) >> atBaseColumn
  atBaseColumn : ParserFn := fun c s =>
    if c.currentColumn s == ctxt.baseColumn then s
    else s.mkErrorAt s!"metadata contents at column {ctxt.baseColumn}" s.pos
  closer :=
    bolThen ctxt (withLeadingHere (eatSpaces >> strFn "%%%")) "%%% (at line beginning)" >>
    withTrailing (eatSpaces >> ignoreFn (chFn '\n' <|> eoiFn) >>
      blockTrailingWs ctxt)

/--
Succeeds when the parser is looking at an ordered list marker.
-/
public def lookaheadOrderedListMarker (ctxt : BlockCtxt) (p : OrderedListType → Int → ParserFn) :
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
          p type n c (s.shrinkStack iniSz |>.setPos numPos)

/--
Succeeds when the parser is looking at an unordered list marker.
-/
public def lookaheadUnorderedListMarker (ctxt : BlockCtxt) (p : UnorderedListType → ParserFn) :
    ParserFn := fun c s =>
  let iniPos := s.pos
  let iniSz := s.stxStack.size
  let s := (onlyBlockOpeners >> takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent) c s
  let markerPos := s.pos
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
    else p type c (s.shrinkStack iniSz |>.setPos markerPos)

def skipUntilDedent (indent : Nat) : ParserFn :=
  skipRestOfLine >>
  manyFn (chFn ' ' >> takeWhileFn (· == ' ') >> guardColumn (· ≥ indent) s!"indentation at {indent}" >> skipRestOfLine)

def recoverUnindent (indent : Nat) (p : ParserFn) (finish : ParserFn := skipFn) :
    ParserFn :=
  recoverFn p (fun _ => ignoreFn (skipUntilDedent indent) >> finish)


mutual
  /-- Parses a list item according to the current nesting context. -/
  public partial def listItemFn (ctxt : BlockCtxt) : ParserFn :=
    withLeadingHere <| nodeFn ``ListItem.item <|
      markerFn >>
      -- An item with no contents is empty. Its marker already recorded the end of its line, so the
      -- block after the list can start.
      withColumnAfterToken fun col =>
        blocksFn {ctxt with minIndent := col}
  where
    -- The marker's trailing whitespace is the padding between it and the item's contents, plus
    -- any blank lines that follow, as with a keyword's trailing space.
    markerTailWs : ParserFn :=
      ignoreFn (lookaheadFn (chFn ' ' <|> chFn '\n')) >> eatSpaces >> lineTailWs
    markerFn :=
      match ctxt.inLists.head? with
      | none => fun _ s => s.mkError "not in a list"
      | some ⟨col, .inr type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          unorderedListMarker type (trailing := markerTailWs)
      | some ⟨col, .inl type⟩ =>
        atomicFn <|
          takeWhileFn (· == ' ') >>
          guardColumn (· == col) s!"indentation at {col}" >>
          orderedListMarker type (trailing := markerTailWs)

  /-- Parses an item from a description list. -/
  public partial def descItemFn (ctxt : BlockCtxt) : ParserFn :=
    withLeadingHere <| nodeFn ``DescItem.item <| withCurrentStackSize fun base =>
      colonFn >>
      withCurrentColumn fun c => textLineFn (recordTrailing := true) >>
      wsFallback lineTailWs base >>
      recoverSkip
        (guardColumnFromNextToken (· ≥ c) s!"description body with indentation at least {c}" >>
          blocks1Fn { ctxt with minIndent := c}) >>
      wsFallback lineTailWs base
  where
    colonFn := atomicFn <|
      takeWhileFn (· == ' ') >>
      guardColumn (· == ctxt.minIndent) s!"indentation at {ctxt.minIndent}" >>
      asTokenFn (chFn ':' false) >> ignoreFn (lookaheadFn (chFn ' '))

  /--
  Parses a block quote.
  -/
  public partial def blockquoteFn (ctxt : BlockCtxt) : ParserFn :=
    atomicFn <| nodeFn ``Block.blockquote <| withCurrentStackSize fun base =>
      takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> chFn '>' >>
      withTrailing eatSpaces >>
      (withColumnAfterToken fun col => blocksFn { ctxt with minIndent := col, topLevel := false }) >>
      -- A blockquote with no contents has no token of its own to record the end of its line, so
      -- the marker records it and the block after the blockquote can start.
      wsFallback (unlessLineEndConsumed (eatSpaces >> optNlWs (blockTrailingWs ctxt))) base

  /-- Parses an unordered list. -/
  public partial def unorderedListFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.ul <|
      lookaheadUnorderedListMarker ctxt fun type =>
        withCurrentColumn fun c =>
          many1Fn (listItemFn {ctxt with minIndent := c + 1, topLevel := false, inLists := ⟨c, .inr type⟩ :: ctxt.inLists})

  /-- Parses an ordered list. -/
  public partial def orderedListFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.ol <|
      lookaheadOrderedListMarker ctxt fun type _start => -- TODO? Validate list numbering?
        withCurrentColumn fun c =>
          many1Fn (listItemFn {ctxt with minIndent := c + 1, topLevel := false, inLists := ⟨c, .inl type⟩ :: ctxt.inLists})

  /-- Parses a definition list. -/
  public partial def definitionListFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.dl <|
      atomicFn (onlyBlockOpeners >> takeWhileFn (· == ' ') >> ignoreFn (lookaheadFn (chFn ':' >> chFn ' ')) >> guardMinColumn ctxt.minIndent) >>
      withCurrentColumn (fun c => many1Fn (descItemFn {ctxt with minIndent := c, topLevel := false}))

  /--
  Parses a paragraph (that is, a sequence of otherwise-undecorated inlines). A paragraph contains
  something other than whitespace, so a run of empty lines is not a paragraph.
  -/
  public partial def paraFn (ctxt : BlockCtxt) : ParserFn := fun c s =>
    let base := s.stxStack.size
    let startPos := s.pos
    -- Non-paragraph blocks take precedence wherever one may open.
    let notBlockOpener :=
      if atBlockStart c s then notFollowedByFn blockOpenerFn "block opener" else skipFn
    (nodeFn ``Block.para <|
      atomicFn (takeWhileFn (· == ' ') >> notBlockOpener >> guardMinColumn ctxt.minIndent s!"paragraph indented at least {ctxt.minIndent}") >>
      textLineFn (recordTrailing := ctxt.recordTrailing) >>
      guardContent base startPos) c s
  where
    guardContent (base : Nat) (startPos : String.Pos.Raw) : ParserFn := fun _ s => Id.run do
      let mut i := base
      while i < s.stxStack.size do
        -- A text line wraps its inlines in one node, so its children are the elements to
        -- inspect.
        let element := s.stxStack.get! i
        let inlines := if element.getKind == nullKind then element.getArgs else #[element]
        for inline in inlines do
          unless blankInline inline do return s
        i := i + 1
      return (s.restore base startPos).mkError "paragraph content"

    blankInline (stx : Syntax) : Bool :=
      match stx.getSubstring? (withLeading := false) (withTrailing := false) with
      | some text => text.all Char.isWhitespace
      | none => false

  /-- Parses a header. -/
  public partial def headerFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.header <|
      guardMinColumn ctxt.minIndent >>
      -- Atomic: confirm this is a header by finding # at beginning of line.
      -- Consumes leading spaces so that errors after this point are not backtracked.
      atomicFn (bol ctxt >> takeWhileFn (· == ' ') >>
        lookaheadFn (skipChFn '#')) >>
      -- Non-backtrackable: the # must be at the base column (or on the first line)
      checkNonIndented >>
      nodeFn ``headerMarker
        (asTokenFn (many1Fn (skipChFn '#')) (skipChFn ' ' >> takeWhileFn (· == ' '))) >>
      lookaheadFn (expectFn (· != '\n') "header text") >>
      textLineFn (allowNewlines := false) (recordTrailing := ctxt.recordTrailing)
  where
    checkNonIndented : ParserFn := fun c s =>
      if atBol ctxt c s then s
      else s.mkErrorAt s!"'#' (header) to start at column {ctxt.baseColumn}" s.pos

  /--
  Parses a code block. The resulting string literal has already had the fences' leading indentation
  stripped.
  -/
  public partial def codeBlockFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.codeblock <| withCurrentStackSize fun base =>
      -- Opener - leaves indent info and open token on the stack. The fence consumes the spaces
      -- that follow it and, when nothing else is on its line, the line's newline.
      withStartPos fun openPos =>
      atomicFn (takeWhileFn (· == ' ') >> guardMinColumn ctxt.minIndent >> pushColumn >>
        nodeFn ``codeBlockFence
          (asTokenFn (atLeastFn 3 (skipChFn '`')) (takeWhileFn (· == ' ') >> optNlWs))) >>
        withIndentColumn fun c =>
          recoverUnindent c <|
            withColumnAfterToken fun c' =>
              let fenceWidth := c' - c
              optionalFn (nameAndArgsFn (tail := argEndWs none >> optNlWs)) >>
              unlessLineEndConsumed (wsFallback (ignoreFn (recoverEolAtErrPos
                (newlineOrUnexpected "positional argument, named argument, flag, or newline")))
                base) >>
              nodeFn versoCodeBlockKind (manyFn (blankCodeLine c <|> codeFrom c fenceWidth)) >>
              unterminatedDelimiterAtEnd openPos c fenceWidth "code block" >>
              closeFence openPos c fenceWidth
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

    -- Consumes up to `col` space characters without recording them, so that the fences'
    -- indentation becomes part of the whitespace between tokens instead of line content.
    eatIndent (col : Nat) : ParserFn := fun c s => Id.run do
      let mut s := s
      for _ in [0:col] do
        let i := s.pos
        if h : c.atEnd i then return s
        else if c.get' i h == ' ' then s := s.next' c i h
        else return s
      return s

    blankCodeLine (col : Nat) : ParserFn :=
      atomicFn <| withLeadingHere (eatIndent col >>
        nodeFn versoCodeBlockLineKind (asTokenFn (takeWhileFn (· == ' ') >> nl)))

    codeFrom (col width : Nat) :=
      atomicFn (bol ctxt >>
        lookaheadFn (ignoreFn (takeWhileFn (· == ' ') >> guardMinColumn col >>
          notFollowedByFn (atLeastFn width (skipChFn '`')) "ending fence"))) >>
      withLeadingHere (eatIndent col >>
        nodeFn versoCodeBlockLineKind
          (asTokenFn (manyFn (satisfyFn (· != '\n') "non-newline") >> satisfyFn (· == '\n') "newline")))

    closeFence (openPos : String.Pos.Raw) (col width : Nat) : ParserFn := fun c s =>
      let fence := String.ofList (.replicate width '`')
      let line := (c.fileMap.toPosition openPos).line
      (bol ctxt >>
       withLeadingHere (takeWhileFn (· == ' ') >>
         guardColumn (· == col)
           s!"closing '{fence}' for the code block opened on line {line} at column {col}" >>
         atomicFn (nodeFn ``codeBlockFence (asTokenFn (repFn width (skipChFn '`'))))) >>
       notFollowedByFn (skipChFn '`') "extra `" >>
       withTrailing (takeWhileFn (· == ' ') >> ignoreFn lineEnd >>
         blockTrailingWs ctxt)) c s

  /-- Parses a directive. -/
  public partial def directiveFn (ctxt : BlockCtxt) : ParserFn :=
    nodeFn ``Block.directive <| withCurrentStackSize fun base =>
      -- Opener - leaves indent info and open token on the stack
      withStartPos fun openPos =>
      atomicFn
        (eatSpaces >> guardMinColumn ctxt.minIndent >>
          nodeFn ``directiveDelimiter (asTokenFn (atLeastFn 3 (skipChFn ':'))) >>
         guardOpenerSize >>
         withTrailing eatSpaces >>
         recoverEolWithAtErrPos #[.missing, .node .none nullKind #[]]
           (nameAndArgsFn (tail := argEndWs none >> optNlWs lineTailWs) >>
            unlessLineEndConsumed (wsFallback
              (ignoreFn (newlineOrUnexpected "positional argument, named argument, flag, or newline"))
              base))) >>
       wsFallback lineTailWs base >>
        (withDelimiterPos 2 fun ⟨l, col⟩ =>
          withDelimiterSize 2 fun delimiterWidth =>
            blocksFn {ctxt with minIndent := col, topLevel := false, maxDirective := delimiterWidth} >>
            recoverHereWith #[.missing]
              (unterminatedDelimiterAtEnd openPos col delimiterWidth "directive" >>
               closeDelimiter l delimiterWidth >>
               withDelimiter 0 fun info _ c s =>
                let actual := (c.fileMap.toPosition info.getPos?.get!).column
                if actual != col then
                  let delim := String.ofList (.replicate delimiterWidth ':')
                  s.mkErrorAt
                    s!"closing '{delim}' for the directive opened on line {l} at column {col}, \
                      but it's at column {actual}"
                    info.getPos?.get!
                else
                  s))

  where
    withDelimiter (atDepth : Nat) (p : SourceInfo → String → ParserFn) : ParserFn := fun c s =>
        match delimiterAtom (s.stxStack.get! (s.stxStack.size - (atDepth + 1))) with
        | .atom info str =>
          if str.all (· == ':') then
            p info str c s
          else
            s.mkError s!"Internal error - index {atDepth} wasn't the directive delimiter - it was the atom {str}"
        | .missing => s.pushSyntax .missing
        | stx =>
          s.mkError s!"Internal error - index {atDepth} wasn't the directive delimiter - it was {stx} in {s.stxStack.back}, {s.stxStack.pop.back}, {s.stxStack.pop.pop.back}, {s.stxStack.pop.pop.pop.back}"

    delimiterAtom : Syntax → Syntax
      | .node _ _ #[a] => a
      | stx => stx

    withDelimiterSize (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withDelimiter atDepth fun _ str => p str.lengthAssumingAscii -- `str` is made up of all `':'`

    withDelimiterPos (atDepth : Nat) (p : Position → ParserFn) : ParserFn :=
      withDelimiter atDepth fun info _ c s => p (c.fileMap.toPosition info.getPos?.get!) c s

    withIndentColumn (atDepth : Nat) (p : Nat → ParserFn) : ParserFn :=
      withDelimiter atDepth fun info _ c s =>
        let col := c.fileMap.toPosition info.getPos?.get! |>.column
        p col c s

    guardOpenerSize : ParserFn := withDelimiterSize 0 fun x =>
        if let some m := ctxt.maxDirective then
          if x < m then skipFn else fun _ s => s.mkError "Too many ':'s here"
        else skipFn

    closeDelimiter (line width : Nat) :=
      let str := String.ofList (.replicate width ':')
      bolThen ctxt (description := s!"closing '{str}' for the directive opened on line {line}")
        (withLeadingHere (eatSpaces >>
          nodeFn ``directiveDelimiter (asTokenFn (strFn str))) >> notFollowedByFn (chFn ':') "':'" >>
         withTrailing (eatSpaces >>
           ignoreFn lineEnd >>
           blockTrailingWs ctxt))

  /--
  Parses a block command.
  -/
  -- This low-level definition is to get exactly the right amount of lookahead
  -- together with column tracking
  public partial def blockCommandFn (ctxt : BlockCtxt) : ParserFn := fun c s =>
    let iniPos := s.pos
    let iniSz := s.stxStack.size
    let restorePosOnErr : ParserState → ParserState
      | ⟨stack, lhsPrec, _, cache, some msg, errs⟩ => ⟨stack, lhsPrec, iniPos, cache, some msg, errs⟩
      | other => other
    let s := eatSpaces c s
    if s.hasError then restorePosOnErr s
    else
      let s := intro c s
      if s.hasError then restorePosOnErr s
      else
        s.mkNode ``Block.command iniSz
  where
    eatSpaces := takeWhileFn (· == ' ')
    intro :=
      guardMinColumn (ctxt.minIndent) >> atomicFn (chFn '{') >> withTrailing eatSpaces >>
      nameAndArgsFn (tail := argEndWs none) (closes := (· == '}')) >>
      nameArgWhitespace none >> chFn '}' >>
      withTrailing (eatSpaces >> ignoreFn lineEnd >>
        blockTrailingWs ctxt)

  /--
  Parses a link reference target.
  -/
  public partial def linkRefFn (c : BlockCtxt) : ParserFn :=
    nodeFn ``Block.link_ref <|
      atLineStart >>
      atomicFn (ignoreFn definitionShape) >>
      chFn '[' >>
      (recoverLineAtErrPos <|
        nodeFn versoRefKind (asTokenFn (refNameFn "a reference name")) >> closeRefNameWith "]:" >>
        withTrailing eatSpaces >>
        nodeFn versoLinkRefUrlKind (asTokenFn urlFn
          (eatSpaces >> ignoreFn lineEnd >>
           blockTrailingWs c)))
  where
    -- Commit earlier for better errors when unambiguous
    atLineStart : ParserFn := fun ctx s =>
      if atBol c ctx s then s
      else if (bracketedName ctx (eatSpaces ctx s)).hasError then
        s.mkErrorAt "link reference definition" s.pos
      else
        let s' := (eatSpaces >> chFn '[') ctx s
        s'.setError { unexpectedTk := s'.stxStack.back, unexpected := misplacedMsg }
    misplacedMsg := "unexpected link reference definition (must be at start of line)"

    /--
    Checks whether the current position begins something that looks sufficiently like a link ref
    definition to be a syntax error if it is not. Commits if so, fails if not. The indentation
    before the definition is consumed.

    This allows fallback in the case of paragraphs that start with text like `[txt][ref]:` or in
    case of footnote defs while still providing good errors on bogus defs like `[ref]: example.com`.
    -/
    definitionShape : ParserFn :=
      bol c >> eatSpaces >> guardMinColumn c.minIndent >> bracketedName

    /--
    Succeeds where a bracketed name is followed by a colon. A `^` after the bracket opens a footnote
    definition instead. The characters between the brackets are read once this succeeds, so one that
    a name may not contain is reported where it stands.
    -/
    bracketedName : ParserFn := fun c s =>
      let ok : Bool := Id.run do
        let mut i := s.pos
        if h : c.atEnd i then return false
        else if c.get' i h != '[' then return false
        else i := c.next i
        if h : c.atEnd i then return false
        else if c.get' i h == '^' then return false
        repeat
          if h : c.atEnd i then return false
          else
            let ch := c.get' i h
            if ch == '\n' then return false
            else if ch == ']' then
              let j := c.next i
              return !c.atEnd j && c.get j == ':'
            else i := c.next i
        return false
      if ok then s else s.mkErrorAt "link reference definition" s.pos

    /--
    Reads the URL, which ends at the last character on the line that is not a space. The spaces
    after it are the token's trailing whitespace.
    -/
    urlFn : ParserFn := fun c s => Id.run do
      let mut stop := s.pos
      let mut i := s.pos
      repeat
        if h : c.atEnd i then break
        else
          let ch := c.get' i h
          if ch == '\n' then break
          else
            i := c.next i
            if ch != ' ' then stop := i
      return s.setPos stop

  /--
  Parses a footnote reference target.
  -/
  public partial def footnoteRefFn (c : BlockCtxt) : ParserFn :=
    nodeFn ``Block.footnote_ref <|
      atomicFn (ignoreFn (bol c >> eatSpaces >> guardMinColumn c.minIndent) >> strFn "[^" >>
        nodeFn versoRefKind (asTokenFn (refNameFn "a footnote name")) >>
        strFn "]:") >>
      withTrailing eatSpaces >>
      notFollowedByFn blockOpenerFn "block opener" >> guardMinColumn c.minIndent >>
      textLineFn (recordTrailing := c.recordTrailing)

  /--
  Parses a block.
  -/
  public partial def blockFn (c : BlockCtxt) : ParserFn :=
    noTabs >>
    -- The indentation that each opener consumes before its first token becomes that token's
    -- leading whitespace, whichever alternative commits.
    withLeadingHere (
      expectedFn "block opener (at line start: '#', '>', ':', '*', '-', '+', '1.', '```', '%%%', '{…}')" (
        blockCommandFn c <|> unorderedListFn c <|> orderedListFn c <|> definitionListFn c <|>
        headerFn c <|> codeBlockFn c <|> directiveFn c <|> blockquoteFn c <|>
        linkRefFn c <|> footnoteRefFn c <|> metadataBlockFn c) <|>
      paraFn c)
  where
    /--
    Reports a tab where a block would begin. This check records the error at the tab, consuming it
    so that the message points at the character it is about and the blocks after it still parse.
    -/
    noTabs : ParserFn := fun c s =>
      let s' := eatSpaces c s
      if h : c.atEnd s'.pos then s
      else if c.get' s'.pos h == '\t' then
        let err : Error :=
          { unexpected := "tabs are not allowed; please configure your editor to expand them" }
        -- `skipBlank` skips the tab and the rest of a line with nothing else on it, so that a line
        -- indented with a tab still parses and a line of only whitespace ends the block before it.
        let s'' := skipBlank c (s'.next' c s'.pos h)
        { s'' with recoveredErrors := s''.recoveredErrors.push (s'.pos, s''.stxStack, err) }
      else s

    /--
    Skips a run of whitespace through its last newline, the way a blank line between blocks is
    skipped.
    -/
    skipBlank (c : ParserContext) (s : ParserState) : ParserState := Id.run do
      let mut s := s
      let mut keep := s.pos
      repeat
        let i := s.pos
        if h : c.atEnd i then break
        else
          let ch := c.get' i h
          if ch == ' ' || ch == '\t' then s := s.next' c i h
          else if ch == '\n' then
            s := s.next' c i h
            keep := s.pos
          else break
      return s.setPos keep

  /--
  Parses zero or more blocks. Each block's final token consumes the whitespace that follows it, and
  `blockSepFallback` is used to parse the whitespace after a block whose final token was lost to
  error recovery.
  -/
  public partial def blocksFn (c : BlockCtxt) : ParserFn := fun ctx s =>
    let base := s.stxStack.size
    sepByFn true (blockFn { c with recordTrailing := true }) (blockSepFallback base) ctx s

  /--
  Parses one or more blocks.
  -/
  public partial def blocks1Fn (c : BlockCtxt) : ParserFn := fun ctx s =>
    let base := s.stxStack.size
    sepBy1Fn true (blockFn { c with recordTrailing := true }) (blockSepFallback base) ctx s

  /--
  Parses some number of blank lines followed by zero or more blocks.
  -/
  public partial def documentFn (blockContext : BlockCtxt := {}) : ParserFn := fun c s =>
    let startPos := s.pos
    let base := s.stxStack.size
    let s := (ignoreFn (eatSpaces >> lineTailWs) >>
      blocksFn blockContext >> wsFallback docEndWs base) c s
    if s.hasError then s
    else
      let stx := s.stxStack.back
      let s := s.popSyntax
      let s := s.pushSyntax (extendFirstLeading c.inputString startPos stx)
      s.mkNode ``Parser.document base
end

/--
Whether a Verso element may repeat `ch` to make one delimiter, so that a sequence of them is a
single delimiter rather than several.
-/
private def isGrowableVersoDelimiter (ch : Char) : Bool :=
  ch == '*' || ch == '_' || ch == '`' || ch == ':' || ch == '#'

/-- The end of the run of `ch` that begins at `pos`. -/
private partial def versoRunEnd (ictx : InputContext) (ch : Char) (pos : String.Pos.Raw) :
    String.Pos.Raw :=
  if ictx.atEnd pos || ictx.get pos != ch then pos else versoRunEnd ictx ch (ictx.next pos)

/--
Returns the start and end of the range over which a Verso parse error at `pos` is reported, along
with the error to report. An end position of `none` indicates that the error has no range, but is to
be reported at a single point.

An error that includes an unexpected token is reported at that token's range. When such an error has
no message of its own, as with errors from Lean's own parsers, a message is derived from the token.

Otherwise, the range starts at `pos` and covers the character there, or the whole run of it when a
Verso element repeats that character to make a single delimiter (e.g. `***` for bold text). At the
end of the input, and at a newline, the end is `none`.

Whitespace before the error stays outside the range.
-/
public def locateError (ictx : InputContext) (pos : String.Pos.Raw) (e : Error) :
    String.Pos.Raw × Option String.Pos.Raw × Error :=
  if let some ⟨start, stop⟩ := e.unexpectedTk.getRange? then
    -- A parser that names what it found says it better than the token does, so its message stands.
    let unexpected :=
      if !e.unexpected.isEmpty then
        e.unexpected
      else
        match e.unexpectedTk with
        | .ident .. => "unexpected identifier"
        | .atom _ val => s!"unexpected token '{val}'"
        | _ => "unexpected token"
    (start, some stop, { e with unexpected })
  else if ictx.atEnd pos || ictx.get pos == '\n' then
    (pos, none, e)
  else
    -- A delimiter is a run of its character, so the whole run is one delimiter to mark.
    let ch := ictx.get pos
    let stop := if isGrowableVersoDelimiter ch then versoRunEnd ictx ch pos else ictx.next pos
    (pos, some stop, e)

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
Parses as `ifVerso` if module docs should use Verso syntax, or as `ifNotVerso` otherwise.
Checks `doc.verso.module` if explicitly set, otherwise falls back to `doc.verso`.
-/
public def ifVersoModuleDocsFn (ifVerso ifNotVerso : ParserFn) : ParserFn := fun c s =>
  let useVerso :=
    if c.options.contains `doc.verso.module then
      c.options.getBool `doc.verso.module
    else
      c.options.getBool `doc.verso
  if useVerso then ifVerso c s
  else ifNotVerso c s

@[inherit_doc ifVersoModuleDocsFn]
public def ifVersoModuleDocs (ifVerso ifNotVerso : Parser) : Parser where
  fn := ifVersoModuleDocsFn ifVerso.fn ifNotVerso.fn

/--
Formatter for `ifVersoModuleDocs`—formats according to the underlying formatters.
-/
@[combinator_formatter ifVersoModuleDocs, expose]
public def ifVersoModuleDocs.formatter (f1 f2 : Formatter) : Formatter := f1 <|> f2

/--
Parenthesizer for `ifVersoModuleDocs`—parenthesizes according to the underlying parenthesizers.
-/
@[combinator_parenthesizer ifVersoModuleDocs, expose]
public def ifVersoModuleDocs.parenthesizer (p1 p2 : Parenthesizer) : Parenthesizer := p1 <|> p2

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
