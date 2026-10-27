/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
module

prelude
import Init.While
import Init.Data.Vector.Basic
public import Lean.Data.Markdown.Basic
public import Lean.Data.Markdown.InlineSource

namespace Lean.Markdown


/-!
## Emphasis matching (CommonMark §6.2)

Implements CommonMark's delimiter stack algorithm.

The entry point is `processEmphasis`, which consumes a flat sequence of `InlineTok`s. Each is either
a fully-finalized non-emphasis `Inline` or a raw `*`/`_` delimiter sequence. It returns the final
`Array Inline` with all matched emphasis spans wrapped as `.bold` or `.italic`. Tokens of the input
are produced by the tokenizer in `Lean.Data.Markdown.Parser.Inline`; this module is the second half
of the inline element parsing pass.

With the `latexMath` extension, the tokens also include `$` delimiter sequences.
-/

variable {s : String.Slice}

/-- The subslice of the `n` delimiter characters at `p`. -/
def delimiterSubslice (p : s.Pos) (n : Nat) : s.Subslice :=
  s.subslice p (p.nextn n) String.Slice.Pos.le_nextn

/--
A sequence of `*` or `_` delimiter characters (a delimiter run, in the CommonMark specification's
terms), classified by the CommonMark left/right-flanking rules.

With the `latexMath` extension, delimiters may also be a sequence of one or two `$`.
-/
public structure DelimSequence (s : String.Slice) where
  /-- Position of the first delimiter character. -/
  startPos : s.Pos
  /-- The delimiter character (`*`, `_`, or `$`). -/
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
that awaits matching.
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
An opening delimiter sequence on the delimiter stack whose characters have not all been matched. Its
still-unmatched characters are a text inline in the output at `outIdx`, and the inlines after that
index are the content that a match wraps.
-/
structure OpenerFrame (s : String.Slice) where
  ch : Char
  /-- Position of the leftmost still-available delimiter character. -/
  startPos : s.Pos
  /-- Original total length of the opening sequence. -/
  origLen : Nat
  /--
  The number of delimiter characters that have not yet been consumed. The available chars are the
  leftmost `remaining` chars; matches consume from the right.
  -/
  remaining : Nat
  /-- Whether the original sequence could close. -/
  canClose : Bool
  /-- The index in the output of the text inline for the still-unmatched delimiter characters. -/
  outIdx : Nat
deriving Inhabited

/-!
### Delimiter matching

CommonMark §6.2 specifies emphasis matching as an algorithm over a *delimiter stack*: each `*`/`_`
sequence that could open emphasis is pushed on the stack while non-delimiter inlines are added to
the inline output, and for each closing sequence the stack is searched downward for a compatible
opener.
The spec describes the algorithm imperatively over two pieces of state, the delimiter stack and the
inline output, and those are maintained in a single `DelimiterMatchState` structure.

As in the specification, an opener's delimiter characters are a text inline in the output, and its
frame records that inline's index. The content of a matched emphasis is the output after the index,
abandoning an opener leaves its text in place, and `openersBottom` bounds each search for an opener
below the point where the last search for the same kind of closer failed.
-/

/--
The index into `openersBottom` for a closer: by its character, its original length modulo 3, and
whether it can also open emphasis, which are the properties that decide whether an opener can match
it.
-/
def bottomKey (seq : DelimSequence s) : Fin 12 :=
  let lenMod3 : Fin 12 :=
    ⟨seq.origLen % 3, Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)⟩
  (if seq.ch == '*' then 0 else 6) + lenMod3 * 2 + (if seq.canOpen then 1 else 0)

/--
The state that is maintained while running CommonMark §6.2's delimiter matching algorithm: the
delimiter stack and the inline output.
-/
structure DelimiterMatchState (s : String.Slice) where
  /-- The delimiter stack: openers whose sequences have not yet been matched, innermost last. -/
  delimiters : Array (OpenerFrame s)
  /-- The inlines that have been emitted so far, including the text of the openers on the stack. -/
  output : Array (Inline s)
  /--
  The pending math openers, most recent last, each with its position, its length, and the index in
  the output of its text inline. Empty unless the `latexMath` extension is enabled.
  -/
  mathOpeners : Array (s.Pos × Nat × Nat)
  /--
  For each kind of closer, the index into `delimiters` at which the search for an opener to match a
  closer of that kind begins; openers below that index are skipped.

  Whether an opener can match a closer depends on three properties of the closer: its delimiter
  character (`*` or `_`), its length modulo 3, and whether it could also open emphasis. The 12
  combinations of these properties are the kinds of closer, numbered by `bottomKey`.

  When the search for an opener to match a closer fails, the openers that are on the stack would
  fail to match a later closer of the same kind too, so the entry for that kind becomes the stack's
  current size.
  -/
  openersBottom : Vector Nat 12

/-- The empty initial state. -/
def DelimiterMatchState.empty : DelimiterMatchState s :=
  { delimiters := #[], output := #[], mathOpeners := #[], openersBottom := Vector.replicate 12 0 }

/--
The monad for §6.2's delimiter matching algorithm.
-/
abbrev DelimM (s : String.Slice) :=
  ReaderT (InlineContext s) (StateM (DelimiterMatchState s))

/--
Merges each text inline of `inlines` that begins where the preceding text inline ends into it, so
that literal brackets and unmatched delimiters join the text around them.
-/
def coalesceText (inlines : Array (Inline s)) : Array (Inline s) :=
  inlines.foldl (init := Array.emptyWithCapacity inlines.size) fun acc inl =>
    match inl, acc.back? with
    | .text r, some (.text r') =>
      if r'.endExclusive == r.startInclusive then
        acc.pop.push (.text (subsliceClamped r'.startInclusive r.endExclusive))
      else acc.push inl
    | _, _ => acc.push inl

/-- Adds a finalized inline to the output. -/
def emit (inl : Inline s) : DelimM s Unit := modify fun st =>
  { st with output := st.output.push inl }

/--
Pushes an opener onto the delimiter stack, with its delimiter characters as a text inline in the
output. Openers that were popped since the last search leave `openersBottom` bounds above the stack,
which are lowered to the stack's size.
-/
def openDelimiter (ch : Char) (startPos : s.Pos) (origLen remaining : Nat) (canClose : Bool) :
    DelimM s Unit := modify fun st =>
  let size := st.delimiters.size
  { st with
    output := st.output.push (.text (delimiterSubslice startPos remaining))
    delimiters := st.delimiters.push
      { ch, startPos, origLen, remaining, canClose, outIdx := st.output.size }
    openersBottom := st.openersBottom.map (min · size) }

/--
Abandons the topmost delimiter. Its still-unmatched characters stay in the output as text, so this
is a pop of the delimiter stack.

This is used both when a closer's match leaves unmatched openers above it on the stack and at the
end, when every opener still on the stack is abandoned.
-/
def abandonOpener : DelimM s Unit := modify fun st =>
  { st with delimiters := st.delimiters.pop }

/--
Wraps the output after the topmost opener as `.bold` (when `matchLen == 2`) or `.italic` (when
`matchLen == 1`) using `openDelim`/`closeDelim` as its delimiters, and then either drops the opener
or shrinks its text to the characters that remain.

Precondition: the delimiter stack is non-empty and its top is the opener that was chosen to match
this closer (any unmatched openers above it have already been abandoned).
-/
def closeMatched (matchLen : Nat) (openDelim closeDelim : s.Subslice) :
    DelimM s Unit := do
  let opener := (← get).delimiters.back!
  let newRem := opener.remaining - matchLen
  modify fun st =>
    let content := coalesceText (st.output.extract (opener.outIdx + 1) st.output.size)
    let wrapped : Inline s :=
      if matchLen == 2 then .bold openDelim content closeDelim
      else .italic openDelim content closeDelim
    -- A matched emphasis span discards the math openers inside it.
    let mathOpeners := st.mathOpeners.filter fun (_, _, outIdx) => outIdx ≤ opener.outIdx
    if newRem == 0 then
      { st with
        output := (st.output.shrink opener.outIdx).push wrapped
        delimiters := st.delimiters.pop
        mathOpeners }
    else
      { st with
        output := (st.output.shrink (opener.outIdx + 1))
          |>.set! opener.outIdx (.text (delimiterSubslice opener.startPos newRem))
          |>.push wrapped
        delimiters := st.delimiters.pop.push { opener with remaining := newRem }
        mathOpeners }

/--
Abandons every opener still on the stack and returns the final inline output. This is the final step
of the spec's procedure, which removes every delimiter still on the stack.
-/
def finalizeEmphasis : DelimM s (Array (Inline s)) := do
  modify fun st => { st with delimiters := #[] }
  return coalesceText (← get).output

/--
Searches the delimiter stack top-down, stopping above index `bottom`, for an opener that is
compatible with the closer `seq`, honoring CommonMark §6.2's rule about lengths that are a multiple
of 3. Returns the index (from the bottom) of the first compatible opener, or `none`.
-/
def findMatchingOpener (stack : Array (OpenerFrame s)) (seq : DelimSequence s) (bottom : Nat) :
    Option Nat := Id.run do
  let mut i := stack.size
  while i > bottom do
    i := i - 1
    let some opener := stack[i]? | return none
    if opener.ch == seq.ch then
      let lenSum := opener.origLen + seq.origLen
      let bothCanBoth := opener.canClose || seq.canOpen
      let blocked :=
        bothCanBoth && lenSum % 3 == 0 &&
        (opener.origLen % 3 != 0 || seq.origLen % 3 != 0)
      unless blocked do
        return some i
  return none

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
    let key := bottomKey seq
    while seqRem > 0 do
      let st ← get
      match findMatchingOpener st.delimiters seq st.openersBottom[key] with
      | none =>
        -- No opener on the stack can match this kind of closer, so later searches for the same
        -- kind start above the current stack.
        modify fun st => { st with openersBottom := st.openersBottom.set key st.delimiters.size }
        break
      | some idx =>
        while (← get).delimiters.size > idx + 1 do
          abandonOpener
        let opener := (← get).delimiters.back!
        let matchLen := if opener.remaining >= 2 && seqRem >= 2 then 2 else 1
        let openDelim :=
          delimiterSubslice (opener.startPos.nextn (opener.remaining - matchLen)) matchLen
        let closeDelim := delimiterSubslice seqStart matchLen
        closeMatched matchLen openDelim closeDelim
        seqRem := seqRem - matchLen
        seqStart := seqStart.nextn matchLen
  if seqRem > 0 then
    if seq.canOpen then
      openDelimiter seq.ch seqStart seq.origLen seqRem seq.canClose
    else
      emit <| .text (delimiterSubslice seqStart seqRem)

/--
Processes one `$` delimiter sequence.

A sequence that can close matches the most recent pending opener when the two have the same
length. The output since that opener becomes the content of the math, taken verbatim from the
source, and every pending opener inside it is discarded.

A sequence that can open becomes a pending opener, and any other sequence is text.
-/
def processMathSequence (seq : DelimSequence s) : DelimM s Unit := do
  let st ← get
  let dollars := delimiterSubslice seq.startPos seq.origLen
  if seq.canClose then
    if let some (openStart, openLen, outIdx) := st.mathOpeners.back? then
      if openLen == seq.origLen then
        let openDollars := delimiterSubslice openStart openLen
        let content := (← inlineSource).linesBetween (openStart.nextn openLen) seq.startPos
        let math : Inline s := .math openDollars ⟨content⟩ dollars (seq.origLen == 2)
        let delimiters := st.delimiters.filter (·.outIdx < outIdx)
        set { st with
          output := (st.output.shrink outIdx).push math
          delimiters
          openersBottom := st.openersBottom.map (min · delimiters.size)
          mathOpeners := #[] }
        return
  if seq.canOpen then
    set { st with
      output := st.output.push (.text dollars)
      mathOpeners := st.mathOpeners.push (seq.startPos, seq.origLen, st.output.size) }
  else
    emit (.text dollars)

/--
Processes the delimiter sequences in `toks`, producing a final flat inline array.

Implements CommonMark §6.2's delimiter-matching algorithm for emphasis (including the rule about
lengths that are a multiple of 3), as well as the LaTeX math extension if enabled. Unmatched
delimiters fall back to literal text.
-/
public def processEmphasis (ctx : InlineContext s) (toks : Array (InlineTok s)) :
    Array (Inline s) :=
  let go : DelimM s (Array (Inline s)) := do
    for tok in toks do
      match tok with
      | .inline inl => emit inl
      | .delim seq =>
        if seq.ch == '$' then processMathSequence seq else processDelimSequence seq
    finalizeEmphasis
  go.run ctx |>.run' .empty
