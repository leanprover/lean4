/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init.While
import Lean.Syntax
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown

/-!
## Emphasis matching (CommonMark §6.2)

Implements CommonMark's emit-as-you-go delimiter stack algorithm.

The single public entry point is `processEmphasis`, which consumes a flat sequence of `InlineTok`s.
Each is either a fully-finalized non-emphasis `Inline` or a raw `*`/`_` delimiter sequence. It returns
the final `Array Inline` with all matched emphasis spans wrapped as `.bold` or `.italic`. Tokens of
the input are produced by the tokenizer in `Markdown.Parser.Inline`; this module is the second half
of the inline element parsing pass.
-/

/--
A sequence of `*` or `_` delimiter characters (a delimiter run, in the CommonMark specification's
terms), classified by the CommonMark left/right-flanking rules.
-/
public structure DelimSequence where
  /-- Position of the first delimiter character. -/
  startPos : String.Pos.Raw
  /-- Position one past the last delimiter character. -/
  endPos : String.Pos.Raw
  /-- The delimiter character (`*` or `_`). -/
  ch : Char
  /-- Number of consecutive delimiter characters. -/
  origLen : Nat
  /-- Whether this sequence can open emphasis. -/
  canOpen : Bool
  /-- Whether this sequence can close emphasis. -/
  canClose : Bool
deriving Inhabited

/--
An intermediate token: either a finalized non-emphasis inline, or a raw emphasis delimiter sequence
awaiting matching.
-/
public inductive InlineTok where
  | inline (i : Inline)
  | delim (seq : DelimSequence)
deriving Inhabited

/--
Appends a `text` inline as an `InlineTok` for `[textStart:pos)` to `out`,
if non-empty.
-/
public def pushTokText (out : Array InlineTok) (textStart pos : String.Pos.Raw) :
    Array InlineTok :=
  if textStart < pos then
    out.push (.inline (.text { start := textStart, stop := pos }))
  else out

/--
An open emphasis context on the processing stack that contains a still-active opening delimiter sequence
with the inline content accumulated since it was pushed.
-/
structure OpenerFrame where
  ch : Char
  /-- Position of the leftmost still-available delimiter character. -/
  startPos : String.Pos.Raw
  /-- Original total length of the opening sequence. -/
  origLen : Nat
  /--
  The number of delimiter characters not yet consumed. The available chars are the leftmost
  `remaining` chars; matches consume from the right.
  -/
  remaining : Nat
  /-- Whether the original sequence could close. -/
  canClose : Bool
  /-- Inlines accumulated since this opener was pushed. -/
  acc : Array Inline
deriving Inhabited

/-!
### Delimiter matching

CommonMark §6.2 specifies emphasis matching as an algorithm over a *delimiter stack*: each `*`/`_`
sequence that could open emphasis is pushed on the stack while non-delimiter inlines are added to the
inline output, and a closing sequence looks down the stack for a compatible opener to match against. The
spec describes the algorithm imperatively over two pieces of state, the delimiter stack and the
inline output, and those are maintained in a single `DelimiterMatchState` structure.

This implementation differs slightly from the spec's pseudocode in that it doesn't keep the inlines
emitted *inside* an open emphasis on the output list and re-walk them on close; instead, they are
kept in the opener itself, so when the opener matches we already have its children ready to wrap.
-/

/--
The state maintained while running CommonMark §6.2's delimiter-matching algorithm: the delimiter
stack, plus the inline output emitted at the document scope (i.e., outside any currently-open
emphasis).

Each currently-open emphasis candidate is stored in `delimiters` and collects its in-progress
children in its `acc` field; only when the opener's sequence is fully matched (or abandoned) do those
children make it into a wrapping node and flow into the parent scope (the next opener's `acc`, or
`output` if the stack is empty).
-/
structure DelimiterMatchState where
  /-- The delimiter stack: openers whose sequences have not yet been matched. -/
  delimiters : Array OpenerFrame
  /-- Inlines emitted at document scope, outside any open emphasis. -/
  output : Array Inline

/-- The empty initial state. -/
def DelimiterMatchState.empty : DelimiterMatchState :=
  { delimiters := #[], output := #[] }

/-- The state monad for §6.2's delimiter-matching algorithm. -/
abbrev DelimM := StateM DelimiterMatchState

/--
Adds a finalized inline to the inline output. It goes into the topmost delimiter's `acc` if the stack
is non-empty, otherwise into the bottom output.
-/
def emit (inl : Inline) : DelimM Unit := modify fun st =>
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    { st with delimiters := st.delimiters.pop.push { top with acc := top.acc.push inl } }
  else
    { st with output := st.output.push inl }

/-- Adds a batch of finalized inlines to the inline output (see `emit`). -/
def emitMany (xs : Array Inline) : DelimM Unit := modify fun st =>
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    { st with delimiters := st.delimiters.pop.push { top with acc := top.acc ++ xs } }
  else
    { st with output := st.output ++ xs }

/--
Pushes a new opener onto the delimiter stack.
-/
def openDelimiter (f : OpenerFrame) : DelimM Unit :=
  modify fun st => { st with delimiters := st.delimiters.push f }

/--
Abandons the topmost delimiter: its still-unmatched delimiter characters are re-emitted as literal
text, and the inlines that accumulated inside the would-be emphasis are flushed to the parent scope
without any emphasis node around them. The spec's procedure removes such a delimiter from the stack
and leaves its characters in place as text. The flush is necessary because we stage in-progress
children on the opener's `acc` field; in the spec's pseudocode they would already sit on the output
list and abandoning would be a stack pop alone.

This is used both when a closer's match leaves unmatched openers above it on the stack and at the
end, when every opener still on the stack is abandoned.
-/
def abandonOpener : DelimM Unit := do
  let st ← get
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    let asInlines : Array Inline :=
      if top.remaining > 0 then
        let textRange : Syntax.Range := {
          start := top.startPos
          -- All delimiter characters are single-byte
          stop  := { byteIdx := top.startPos.byteIdx + top.remaining }
        }
        #[Inline.text textRange] ++ top.acc
      else top.acc
    set { st with delimiters := st.delimiters.pop }
    emitMany asInlines

/--
Wraps the topmost delimiter's accumulated tokens as `.bold` (when `matchLen == 2`) or `.italic`
(when `matchLen == 1`) using `openDelim`/`closeDelim` as its source ranges, and then either drops
the opener or removes the part that was consumed.

Precondition: the delimiter stack is non-empty and its top is the opener chosen to match this closer
(any unmatched openers above it have already been abandoned).
-/
def closeMatched (matchLen : Nat) (openDelim closeDelim : Syntax.Range) :
    DelimM Unit := do
  let opener := (← get).delimiters.back!
  let wrapped : Inline :=
    if matchLen == 2 then .bold openDelim opener.acc closeDelim
    else .italic openDelim opener.acc closeDelim
  let newRem := opener.remaining - matchLen
  if newRem == 0 then
    modify fun st => { st with delimiters := st.delimiters.pop }
    emit wrapped
  else
    modify fun st =>
      { st with
        delimiters :=
          st.delimiters.pop.push { opener with remaining := newRem, acc := #[wrapped] } }

/--
Abandons every opener still on the stack and returns the final inline output. This is the final step
of the spec's procedure, which removes every delimiter still on the stack.
-/
def finalizeEmphasis : DelimM (Array Inline) := do
  repeat
    if (← get).delimiters.isEmpty then break
    abandonOpener
  return (← get).output

/--
Scans the delimiter stack top-down for an opener compatible with the closer `seq`, honoring
CommonMark §6.2's rule about lengths that are a multiple of 3. Returns the index (from the bottom)
of the first compatible opener, or `none`.
-/
def findMatchingOpener (stack : Array OpenerFrame) (seq : DelimSequence) : Option Nat := do
  for h : i in [0:stack.size] do
      have : stack.size > 0 := Nat.zero_lt_of_lt h.2.1
      let opener := stack[stack.size - (i + 1)]'(Nat.sub_lt this (Nat.zero_lt_succ i))
      if opener.ch == seq.ch then
        let lenSum := opener.origLen + seq.origLen
        let bothCanBoth := opener.canClose || seq.canOpen
        let blocked :=
          bothCanBoth && lenSum % 3 == 0 &&
          (opener.origLen % 3 != 0 || seq.origLen % 3 != 0)
        unless blocked do
          return stack.size - (i + 1)
    failure

/--
Processes one delimiter sequence from the token stream. If possible, it uses it as a closer,
repeatedly matching it against compatible openers on the stack and abandoning any unmatched openers
above each match. If any chars remain in the sequence, they are pushed if the sequence can open
emphasis, or emitted as text otherwise.
-/
def processDelimSequence (seq : DelimSequence) : DelimM Unit := do
  let mut seqRem := seq.origLen
  let mut seqStart := seq.startPos
  if seq.canClose then
    let mut keepTrying := true
    while seqRem > 0 && keepTrying do
      match findMatchingOpener (← get).delimiters seq with
      | none => keepTrying := false
      | some idx =>
        while (← get).delimiters.size > idx + 1 do
          abandonOpener
        let opener := (← get).delimiters.back!
        let matchLen := if opener.remaining >= 2 && seqRem >= 2 then 2 else 1
        let openDelim : Syntax.Range := {
          -- All delimiter characters are single-byte, so this arithmetic makes sense
          start := { byteIdx := opener.startPos.byteIdx + opener.remaining - matchLen }
          stop  := { byteIdx := opener.startPos.byteIdx + opener.remaining }
        }
        let closeDelim : Syntax.Range := {
          start := seqStart
          -- Delimiter characters are all single-byte, so adding matchLen is sensible here
          stop  := { byteIdx := seqStart.byteIdx + matchLen }
        }
        closeMatched matchLen openDelim closeDelim
        seqRem := seqRem - matchLen
        seqStart := { byteIdx := seqStart.byteIdx + matchLen }
  if seqRem > 0 then
    if seq.canOpen then
      openDelimiter {
        ch := seq.ch
        startPos := seqStart
        origLen := seqRem
        remaining := seqRem
        canClose := seq.canClose
        acc := #[]
      }
    else
      -- The remainder length seqRem is in characters, but all delimiters in the sequence are single-byte
      emit <|
        .text { start := seqStart, stop := { byteIdx := seqStart.byteIdx + seqRem } }

/--
Processes the emphasis delimiter sequences in `toks`, producing a final flat inline array. Implements
CommonMark §6.2's delimiter-matching algorithm (including the rule about lengths that are a multiple
of 3). Unmatched delimiters are turned into literal text.
-/
public def processEmphasis (toks : Array InlineTok) : Array Inline :=
  let go : DelimM (Array Inline) := do
    for tok in toks do
      match tok with
      | .inline inl => emit inl
      | .delim seq => processDelimSequence seq
    finalizeEmphasis
  go.run' .empty
