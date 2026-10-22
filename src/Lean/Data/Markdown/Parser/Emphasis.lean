/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init.While
public import Lean.Data.Markdown.Basic

namespace Lean.Markdown


/-!
## Emphasis matching (CommonMark §6.2)

Implements CommonMark's emit-as-you-go delimiter stack algorithm.

The entry point is `processEmphasis`, which consumes a flat sequence of `InlineTok`s. Each is either
a fully-finalized non-emphasis `Inline` or a raw `*`/`_` delimiter sequence. It returns the final
`Array Inline` with all matched emphasis spans wrapped as `.bold` or `.italic`. Tokens of the input
are produced by the tokenizer in `Lean.Data.Markdown.Parser.Inline`; this module is the second half
of the inline element parsing pass.
-/

variable {s : String.Slice}

/-- The subslice of the `n` delimiter characters at `p`. -/
def delimiterSubslice (p : s.Pos) (n : Nat) : s.Subslice :=
  s.subslice p (p.nextn n) String.Slice.Pos.le_nextn

/--
A sequence of `*` or `_` delimiter characters (a delimiter run, in the CommonMark specification's
terms), classified by the CommonMark left/right-flanking rules.
-/
public structure DelimSequence (s : String.Slice) where
  /-- Position of the first delimiter character. -/
  startPos : s.Pos
  /-- Position one past the last delimiter character. -/
  endPos : s.Pos
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
public inductive InlineTok (s : String.Slice) where
  | inline (i : Inline s)
  | delim (seq : DelimSequence s)
deriving Inhabited

/--
Appends a `text` inline as an `InlineTok` for `[textStart:pos)` to `out`,
if non-empty.
-/
public def pushTokText (out : Array (InlineTok s)) (textStart pos : s.Pos) :
    Array (InlineTok s) :=
  if textStart < pos then
    out.push (.inline (.text (subsliceClamped textStart pos)))
  else out

/--
An open emphasis context on the processing stack that contains a still-active opening delimiter
sequence with the inline content accumulated since it was pushed.
-/
structure OpenerFrame (s : String.Slice) where
  ch : Char
  /-- Position of the leftmost still-available delimiter character. -/
  startPos : s.Pos
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
  acc : Array (Inline s)
deriving Inhabited

/-!
### Delimiter matching

CommonMark §6.2 specifies emphasis matching as an algorithm over a *delimiter stack*: each `*`/`_`
sequence that could open emphasis is pushed on the stack while non-delimiter inlines are added to the
inline output, and a closing sequence looks down the stack for a compatible opener to match against.
The spec describes the algorithm imperatively over two pieces of state, the delimiter stack and the
inline output, and those are maintained in a single `DelimiterMatchState` structure.

Inlines emitted inside an open emphasis are kept in its opener frame, so when the opener matches,
its children are ready to wrap.
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
structure DelimiterMatchState (s : String.Slice) where
  /-- The delimiter stack: openers whose sequences have not yet been matched. -/
  delimiters : Array (OpenerFrame s)
  /-- Inlines emitted at document scope, outside any open emphasis. -/
  output : Array (Inline s)

/-- The empty initial state. -/
def DelimiterMatchState.empty : DelimiterMatchState s :=
  { delimiters := #[], output := #[] }

/-- The state monad for §6.2's delimiter-matching algorithm. -/
abbrev DelimM (s : String.Slice) := StateM (DelimiterMatchState s)

/--
Adds a finalized inline to the inline output. It goes into the topmost delimiter's `acc` if the stack
is non-empty, otherwise into the bottom output.
-/
def emit (inl : Inline s) : DelimM s Unit := modify fun st =>
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    { st with delimiters := st.delimiters.pop.push { top with acc := top.acc.push inl } }
  else
    { st with output := st.output.push inl }

/-- Adds a batch of finalized inlines to the inline output (see `emit`). -/
def emitMany (xs : Array (Inline s)) : DelimM s Unit := modify fun st =>
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    { st with delimiters := st.delimiters.pop.push { top with acc := top.acc ++ xs } }
  else
    { st with output := st.output ++ xs }

/--
Pushes a new opener onto the delimiter stack.
-/
def openDelimiter (f : OpenerFrame s) : DelimM s Unit :=
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
def abandonOpener : DelimM s Unit := do
  let st ← get
  if h : st.delimiters.size > 0 then
    let top := st.delimiters.back h
    let asInlines : Array (Inline s) :=
      if top.remaining > 0 then
        #[Inline.text (delimiterSubslice top.startPos top.remaining)] ++ top.acc
      else top.acc
    set { st with delimiters := st.delimiters.pop }
    emitMany asInlines

/--
Wraps the topmost delimiter's accumulated tokens as `.bold` (when `matchLen == 2`) or `.italic`
(when `matchLen == 1`) using `openDelim`/`closeDelim` as its delimiters, and then either drops
the opener or removes the part that was consumed.

Precondition: the delimiter stack is non-empty and its top is the opener chosen to match this closer
(any unmatched openers above it have already been abandoned).
-/
def closeMatched (matchLen : Nat) (openDelim closeDelim : s.Subslice) :
    DelimM s Unit := do
  let opener := (← get).delimiters.back!
  let wrapped : Inline s :=
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
def finalizeEmphasis : DelimM s (Array (Inline s)) := do
  repeat
    if (← get).delimiters.isEmpty then break
    abandonOpener
  return (← get).output

/--
Scans the delimiter stack top-down for an opener compatible with the closer `seq`, honoring
CommonMark §6.2's rule about lengths that are a multiple of 3. Returns the index (from the bottom)
of the first compatible opener, or `none`.
-/
def findMatchingOpener (stack : Array (OpenerFrame s)) (seq : DelimSequence s) : Option Nat := do
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
def processDelimSequence (seq : DelimSequence s) : DelimM s Unit := do
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
        let openDelim := delimiterSubslice (opener.startPos.nextn (opener.remaining - matchLen)) matchLen
        let closeDelim := delimiterSubslice seqStart matchLen
        closeMatched matchLen openDelim closeDelim
        seqRem := seqRem - matchLen
        seqStart := seqStart.nextn matchLen
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
      emit <| .text (delimiterSubslice seqStart seqRem)

/--
Processes the emphasis delimiter sequences in `toks`, producing a final flat inline array. Implements
CommonMark §6.2's delimiter-matching algorithm (including the rule about lengths that are a multiple
of 3). Unmatched delimiters are turned into literal text.
-/
public def processEmphasis (toks : Array (InlineTok s)) : Array (Inline s) :=
  let go : DelimM s (Array (Inline s)) := do
    for tok in toks do
      match tok with
      | .inline inl => emit inl
      | .delim seq => processDelimSequence seq
    finalizeEmphasis
  go.run' .empty
