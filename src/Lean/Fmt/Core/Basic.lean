/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Data.Hashable
public import Init.Data.Ord.Basic
public import Std.Data.HashMap.Basic
import Init.Data

/-!
Document language of the `Fmt` formatter.

This file implements the document language of 'A Pretty Expressive Printer' [1] by
Sorawee Porncharoenwase, Justin Pombrio and Emina Torlak.
This implementation is based on the Racket implementation of pretty-expressive [2].

[1] https://arxiv.org/pdf/2310.01530
[2] https://docs.racket-lang.org/pretty-expressive/
-/

public section

namespace Lean.Fmt

/--
Bitmap that tracks the fullness of the two edge positions of the document that is currently being
resolved by the formatter, i.e. the position immediately *before* the document and the position
immediately *after* it.

A position is *full* if no text may be emitted between it and the end of its line, which is what
`Doc.final` asserts about the position after it, and *initial* if no text may be emitted between
the start of its line and the position, which is what `Doc.initial` asserts about the position
before it. Both properties are tracked independently for both edge positions.

In the formatter, we case split on the fullness state in several places and then prune subtrees
of the search when we notice that they are inconsistent with the actual document currently being
resolved.
-/
@[expose]
def FullnessState := UInt8
deriving Inhabited, BEq, Hashable

@[inline]
def FullnessState.mk
    (isFullBefore : Bool) (isFullAfter : Bool) (isInitialBefore : Bool) (isInitialAfter : Bool)
    : FullnessState :=
  (isInitialBefore.toUInt8 <<< 3) ||| (isInitialAfter.toUInt8 <<< 2)
    ||| (isFullBefore.toUInt8 <<< 1) ||| isFullAfter.toUInt8

@[inline]
def FullnessState.isFullBefore (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b10) != 0

@[inline]
def FullnessState.isFullAfter (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b1) != 0

@[inline]
def FullnessState.isInitialBefore (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b1000) != 0

@[inline]
def FullnessState.isInitialAfter (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (s &&& 0b100) != 0

@[inline]
def FullnessState.setFullBefore (s : FullnessState) (isFullBefore : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111101 : UInt8)) ||| (isFullBefore.toUInt8 <<< 1)

@[inline]
def FullnessState.setFullAfter (s : FullnessState) (isFullAfter : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111110 : UInt8)) ||| isFullAfter.toUInt8

@[inline]
def FullnessState.setInitialBefore (s : FullnessState) (isInitialBefore : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11110111 : UInt8)) ||| (isInitialBefore.toUInt8 <<< 3)

@[inline]
def FullnessState.setInitialAfter (s : FullnessState) (isInitialAfter : Bool) : FullnessState :=
  let s : UInt8 := s
  (s &&& (0b11111011 : UInt8)) ||| (isInitialAfter.toUInt8 <<< 2)

/--
Set of `FullnessState`s, represented as a bitmap in which bit `i` stands for the fullness state
with value `i`.
-/
abbrev FullnessStateSet := UInt16

@[inline]
def FullnessStateSet.contains (set : FullnessStateSet) (s : FullnessState) : Bool :=
  let s : UInt8 := s
  (set >>> s.toUInt16) &&& 1 != 0

@[specialize]
def FullnessStateSet.ofPredBelow (p : FullnessState → Bool)
    : Nat → FullnessStateSet → FullnessStateSet
  | 0, acc =>
    acc
  | i + 1, acc =>
    let s : FullnessState := i.toUInt8
    ofPredBelow p i (if p s then acc ||| ((1 : UInt16) <<< i.toUInt16) else acc)

/-- Yields the set of all fullness states in which `p` holds. -/
@[inline]
def FullnessStateSet.ofPred (p : FullnessState → Bool) : FullnessStateSet := ofPredBelow p 16 0

/--
Given the set `inner` of fullness states of `d` that have some property, yields the set of fullness
states of `final d` in which `isFullAfter` holds and `d` has the property in at least one of the two
fullness states that the formatter resolves `d` in.
-/
@[inline]
def FullnessStateSet.finalAny (inner : FullnessStateSet) : FullnessStateSet :=
  -- `isFullAfter` is bit 0 of a fullness state, so the states in which it holds are the odd ones.
  ((inner <<< 1) ||| inner) &&& 0xAAAA

/--
Like `FullnessStateSet.finalAny`, but `d` must have the property in both fullness states that the
formatter resolves `d` in.
-/
@[inline]
def FullnessStateSet.finalAll (inner : FullnessStateSet) : FullnessStateSet :=
  (inner <<< 1) &&& inner &&& 0xAAAA

/--
Given the set `inner` of fullness states of `d` that have some property, yields the set of fullness
states of `initial d` in which `isInitialBefore` holds and `d` has the property in at least one of
the two fullness states that the formatter resolves `d` in.
-/
@[inline]
def FullnessStateSet.initialAny (inner : FullnessStateSet) : FullnessStateSet :=
  -- `isInitialBefore` is bit 3 of a fullness state, so the states in which it holds are 8 to 15.
  ((inner <<< 8) ||| inner) &&& 0xFF00

/--
Like `FullnessStateSet.initialAny`, but `d` must have the property in both fullness states that the
formatter resolves `d` in.
-/
@[inline]
def FullnessStateSet.initialAll (inner : FullnessStateSet) : FullnessStateSet :=
  (inner <<< 8) &&& inner &&& 0xFF00

/--
Yields the set of fullness states of `append a b` in which `p` holds for the fullness states of `a`
and `b` in at least one of the case splits that the formatter performs on the fullness state of the
position between `a` and `b`.
-/
@[specialize]
def FullnessStateSet.anySplit (p : FullnessState → FullnessState → Bool) : FullnessStateSet :=
  ofPred fun s =>
    let holdsFor (isMidFull isMidInitial : Bool) :=
      p (s.setFullAfter isMidFull |>.setInitialAfter isMidInitial)
        (s.setFullBefore isMidFull |>.setInitialBefore isMidInitial)
    holdsFor false false || holdsFor false true || holdsFor true false || holdsFor true true

/--
Fullness states in which resolving a `newline` node fails.

`newline` ends the current line and starts a new one. The new line can never be full at its
start and the old line can never be initial at its end.
Hence, resolutions in which `isFullAfter` or `isInitialBefore` are true directly at
`newline` fail.
-/
def newlineFailureSet : FullnessStateSet :=
  FullnessStateSet.ofPred fun state => state.isFullAfter || state.isInitialBefore

/--
Whether resolving a `text` node fails in the given `FullnessState`, where `isEmpty` designates
whether its text is empty.
-/
def textFails (isEmpty : Bool) (state : FullnessState) : Bool :=
  -- Fullness and initialness impose the same constraints on `text` in opposite directions.
  let isFailureFor (before after : Bool) :=
    match before, after with
    -- `text` nodes can be placed on non-full lines.
    | false, false =>
      false
    -- `text` nodes cannot turn a line from being full to non-full.
    | true, false =>
      true
    -- `text` nodes cannot turn a line from being non-full to full.
    | false, true =>
      true
    -- Empty text nodes can be inserted on a full line, while non-empty text nodes cannot.
    | true, true =>
      !isEmpty
  isFailureFor state.isFullBefore state.isFullAfter
    || isFailureFor state.isInitialBefore state.isInitialAfter

/--
Fullness states in which resolving a `text` node fails, where `isEmpty` designates whether its text
is empty.
-/
def textFailureSet (isEmpty : Bool) : FullnessStateSet :=
  if isEmpty then emptyTextFailureSet else nonEmptyTextFailureSet
where
  emptyTextFailureSet : FullnessStateSet := FullnessStateSet.ofPred (textFails true)
  nonEmptyTextFailureSet : FullnessStateSet := FullnessStateSet.ofPred (textFails false)

@[expose]
def TagId := Nat
deriving Inhabited, BEq, Hashable, Ord, Repr, ToString, HAdd

inductive Doc.AlwaysEmptiness where
  | alwaysEmpty
  | alwaysEmptyIfFlattened
  | sometimesNonEmpty

def Doc.AlwaysEmptiness.max (e1 e2 : Doc.AlwaysEmptiness) : Doc.AlwaysEmptiness :=
  let v
    | .alwaysEmpty => 0
    | .alwaysEmptyIfFlattened => 1
    | .sometimesNonEmpty => 2
  if v e1 >= v e2 then
    e1
  else
    e2

inductive Doc.AlwaysNonEmptiness where
  | alwaysNonEmpty
  | sometimesEmpty

def Doc.AlwaysNonEmptiness.max (e1 e2 : Doc.AlwaysNonEmptiness) : Doc.AlwaysNonEmptiness :=
  let v
    | .alwaysNonEmpty => 0
    | .sometimesEmpty => 1
  if v e1 >= v e2 then
    e1
  else
    e2

inductive Doc.Atomicness where
  | atomic
  | atomicIfFlattened
  | compoundAtomic
  | compoundAtomicIfFlattened
  | nonAtomic

def Doc.Atomicness.max (e1 e2 : Doc.Atomicness) : Doc.Atomicness :=
  let v
    | .atomic => 0
    | .atomicIfFlattened => 1
    | .compoundAtomic => 2
    | .compoundAtomicIfFlattened => 3
    | .nonAtomic => 4
  if v e1 >= v e2 then
    e1
  else
    e2

structure Assertion where
  assertion : (columnPos : Nat) → (indentation : Nat) → (nonCumulativeIndentation : Nat) → Bool
  id : Name

instance : Repr Assertion where
  reprPrec _ _ := "<assertion>"

/-- Input document consumed by the formatter, which chooses an optimal rendering of the document. -/
inductive Doc (τ : Type) where
  /--
  Indicates that rendering this document is impossible. The formatter will always choose a rendering
  of the document without `failure` nodes if one is available.
  This is sometimes useful when defining custom combinators on a pre-existing document.

  Used when a `flattened` document contains an `unflattenable` node.

  Example:
  ```
  either (text "a") failure
  ```
  produces
  ```
  a
  ```
  -/
  | failure
  /--
  Designates a newline in the document.

  Within `flattened`, all `newline f` nodes are replaced with `text f`. To designate a newline
  that cannot be flattened, wrap it in an `unflattenable` node.

  Any newline that is not flattened by an outer `flattened` node will yield `\n` followed by
  an amount of spaces corresponding to the current level of indentation as set by
  `indented`, `aligned` and `unindented` in the rendered document.

  `f` is irrelevant during formatting: before formatting, a preprocessing step eliminates
  all `flattened` nodes by replacing all `newline f` nodes within each `flattened` node.

  Examples:

  ```
  indented 2 true
    (append
      (append
        (text "a")
        (newline " ")))
      (text "b"))
  ```
  produces
  ```
  a
    b
  ```
  ---
  ```
  flattened
    (append
      (append
        (text "a")
        (newline " ")))
      (text "b"))
  ```
  produces
  ```
  a b
  ```
  -/
  | newline (f : String)
  /--
  Designates a piece of text without newlines in the document.
  `text` nodes are never broken apart by the formatter.

  The formatter will never choose a rendering where a non-empty `text` node is placed on the same
  line after a `final` node or on the same line before an `initial` node.

  Examples:

  ```
  text "foo"
  ```
  produces
  ```
  foo
  ```
  ---
  ```
  either
    (append
      (final (text "a"))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  c
  ```
  ---
  ```
  either
    (append
      (text "b")
      (initial (text "a")))
    (text "c")
  ```
  produces
  ```
  c
  ```
  -/
  | text (s : String)
  /--
  Associates a unique `TagId` with the inner document.
  Tags are used to transfer properties on `Doc` to the rendered document.

  Example:
  ```
  tagged 0 (text "a")
  ```
  produces
  ```
  a
  ```
  where the range `[0, 1]` is tagged with `0`.
  -/
  | tagged (id : TagId) (d : Doc τ)
  /--
  Flattens an inner document by replacing all `newline f` nodes in the inner
  document with `text f` and all `unflattenable` nodes in the inner document with `failure`.

  `flattened` is eliminated before formatting by a preprocessing step that replaces all
  `newline f` nodes within each `flattened` node.

  Examples:

  ```
  flattened
    (append
      (append
        (text "a")
        (newline " ")))
      (text "b"))
  ```
  produces
  ```
  a b
  ```
  ---
  ```
  flattened
    (append
      (append
        (text "a")
        (unflattenable (newline " ")))
      (text "b"))
  ```
  produces
  ```
  <no output>
  ```
  -/
  | flattened (d : Doc τ)
  /--
  Designates an inner document that cannot be flattened.

  When an outer `flattened` node attempts to flatten an `unflattenable` node, the
  `unflattenable` node is replaced with `failure`. Outside of a `flattened` node,
  `unflattenable d` behaves exactly like `d`.

  Like `flattened`, `unflattenable` is eliminated before formatting by a preprocessing step.

  Examples:

  ```
  append
    (append
      (text "a")
      (unflattenable (newline " ")))
    (text "b")
  ```
  produces
  ```
  a
  b
  ```
  ---
  ```
  flattened
    (append
      (append
        (text "a")
        (unflattenable (newline " ")))
      (text "b"))
  ```
  produces
  ```
  <no output>
  ```
  -/
  | unflattenable (d : Doc τ)
  /--
  Adds `n` to the current level of indentation within an inner document.
  Multiple `indented` nodes with `isCumulative = false` will only increase the level of indentation
  once per line, which is useful to request that an inner document needs to be indented if it
  is broken over to another line, without these requests doubling up over multiple nested documents,
  all of which may need to be indented once if they are all on separate lines, but should not be
  indented several times if they end up on the same line. For non-cumulative `indented n ..` nodes
  on the same line, the innermost `n` is used.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation
  (i.e. the level of cumulative indentation + the level of non-cumulative indentation)
  after the newline.

  Examples:

  ```
  indented 2 true
    (append
      (text "a")
      (indented 2 true
        (append
          (append
            (text "b")
            (newline " "))
          (text "c"))))
  ```
  produces
  ```
  ab
      c
  ```
  ---
  ```
  indented 2 false
    (append
      (text "a")
      (append
        (text "b")
        (indented 2 false
          (append
            (newline " ")
            (text "c")))))
  ```
  produces
  ```
  ab
    c
  ```
  ---
  ```
  indented 2 false
    (append
      (text "a")
      (append
        (newline " ")
        (append
          (text "b")
          (indented 2 false
            (append
              (newline " ")
              (text "c"))))))
  ```
  produces
  ```
  a
    b
      c
  ```
  -/
  -- Non-cumulative indentation does not exist in the Racket implementation, but it is very useful
  -- when formatting Lean documents, as each line break in a nested term should only increase the
  -- level of indentation by 1.
  | indented (n : Nat) (isCumulative : Bool) (d : Doc τ)
  /--
  Sets the current level of indentation within an inner document to the current column position
  at the position where the `aligned` is rendered.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Example:

  ```
  append
    (text "a")
    (aligned
      (append
        (newline " ")
        (text "b")))
  ```
  produces
  ```
  a
   b
  ```
  -/
  | aligned (d : Doc τ)
  /--
  Sets the current level of indentation within an inner document to 0.

  When rendering a newline, the formatter produces an amount of spaces corresponding to the
  current level of indentation after the newline.

  Examples:

  ```
  indented 2 true
    (append
      (unindented
        (append
          (text "a")
          (newline " ")))
      (text "b"))
  ```
  produces
  ```
  a
  b
  ```
  -/
  | unindented (onlyNonCumulative : Bool) (d : Doc τ)
  /--
  Enforces that no text can be placed on the same line after the inner document.

  Example:

  ```
  either
    (append
      (final (text "a"))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  c
  ```
  -/
  | final (d : Doc τ)
  /--
  Enforces that no text can be placed on the same line before the inner document.
  The start of the document is treated as the start of a line, so an `initial` node at the very
  beginning of the document is always admissible, independently of the offset it is formatted at.

  Example:

  ```
  either
    (append
      (text "b")
      (initial (text "a")))
    (text "c")
  ```
  produces
  ```
  c
  ```
  -/
  | initial (d : Doc τ)
  /--
  Hides the cost of an inner document from the surrounding document, which is resolved as if
  `free d` was `text ""`.

  The inner document is resolved on its own and a single rendering is chosen for it. That rendering
  is emitted as-is, but its cost is discarded and the column position after it is reset to the
  column position at which it started.

  This is useful for self-contained inner documents, typically ones delimited by newlines such as
  comments, whose width and height should not influence the rendering of the surrounding document.

  Since the column position is reset, the rendering of the inner document should end at the column
  position at which it started, e.g. by ending in a newline. Otherwise, the document following it
  is rendered directly after the inner document, but laid out as if the inner document was empty.

  Examples:

  ```
  either
    (append
      (free (text "aaaaaaaaaa"))
      (text "b"))
    (append
      (free (text "aaaaaaaaaa"))
      (append nl (text "b")))
  ```
  (assuming a lawful cost function and a page width limit of 5) produces
  ```
  aaaaaaaaaab
  ```
  ---
  ```
  either
    (append
      (text "aaaaaaaaaa")
      (text "b"))
    (append
      (text "aaaaaaaaaa")
      (append nl (text "b")))
  ```
  (assuming a lawful cost function and a page width limit of 5) produces
  ```
  aaaaaaaaaa
  b
  ```
  -/
  | free (d : Doc τ)
  /--
  Yields the inner document if the assertion holds or fails otherwise.

  The assertion is a predicate over the current column position, the level of (cumulative)
  indentation and the level of non-cumulative indentation at that position.
  Hence, whether resolving a document that contains `guarded` fails can depend on the resolution
  context, which the formatter tracks with `Doc.hasContextDependentFailure`.

  Example:

  ```
  append
    (text "a")
    (either
      (guarded (fun columnPos _ _ => columnPos == 0) (text "b"))
      (guarded (fun columnPos _ _ => columnPos != 0) (text "c"))
  ```
  produces
  ```
  ac
  ```
  -/
  | guarded (p : Assertion) (d : Doc τ)
  /--
  Adds `cost` to the cost of every rendering of the inner document.
  Since the formatter chooses a rendering with an optimal cost, this can be used to bias the
  formatter towards or against choosing certain alternatives.
  -/
  | costing (cost : τ) (d : Doc τ)
  /--
  Designates a document that can be rendered to one of two alternatives.

  The formatter will always choose a non-failing alternative if one is available or fail otherwise.
  When both alternatives are not failing, it chooses an optimal rendering from both alternatives.

  If the two subtrees of an `either` have the same structure, then this structure should be
  referentially shared between the two subtrees instead of duplicating them. This ensures that
  documents with lots of alternatives can still be formatted efficiently, as the formatter will be
  able to re-use state across these alternatives.

  Examples:

  ```
  either (text "a") failure
  ```
  produces
  ```
  a
  ```
  ---
  ```
  either
    (text "a")
    (append
      (append
        (text "b")
        (newline " "))
      (text "c"))
  ```
  (assuming a lawful cost function) produces
  ```
  a
  ```
  -/
  | either (a b : Doc τ)
  /--
  Appends the second document to the last line of the first document.

  Example:

  ```
  append
    (append
      (append
        (text "a")
        (newline " "))
      (text "b"))
    (text "c")
  ```
  produces
  ```
  a
  bc
  ```
  -/
  | append (a b : Doc τ)
with
  /--
  Designates an underapproximation of the set of fullness states in which resolving the
  preprocessed document fails in every resolution context. For documents without `guarded`, this
  set is exact, so the formatter can prune all failing alternatives before resolving them.
  -/
  @[computed_field]
  failureSet : (τ : Type) → Doc τ → FullnessStateSet
    | _, .failure =>
      0xFFFF
    | _, .newline .. =>
      newlineFailureSet
    | _, .text s =>
      textFailureSet s.isEmpty
    -- Eliminated during preprocessing.
    | _, .flattened _
    | _, .unflattenable _ =>
      0
    -- Whether the assertion of `guarded` holds depends on the resolution context.
    | _, .guarded _ d
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .free d
    | _, .costing _ d =>
      failureSet _ d
    -- `final` fails if `isFullAfter` (bit 0) does not hold, and otherwise if `d` fails in both
    -- fullness states that it is resolved in.
    | _, .final d =>
      0x5555 ||| FullnessStateSet.finalAll (failureSet _ d)
    -- `initial` fails if `isInitialBefore` (bit 3) does not hold, and otherwise if `d` fails in both
    -- fullness states that it is resolved in.
    | _, .initial d =>
      0x00FF ||| FullnessStateSet.initialAll (failureSet _ d)
    | _, .either a b =>
      failureSet _ a &&& failureSet _ b
    | _, .append a b =>
      let failureA := failureSet _ a
      let failureB := failureSet _ b
      if failureA == 0xFFFF || failureB == 0xFFFF then
        0xFFFF
      else
        ~~~(FullnessStateSet.anySplit fun s1 s2 =>
          ! FullnessStateSet.contains failureA s1 && ! FullnessStateSet.contains failureB s2)
  /--
  Designates an overapproximation for the amount of newlines in a document.
  This is used by the formatter to choose renderings amongst multiple alternatives
  that all exceed a maximum optimality cutoff width, which bounds the total search space.
  -/
  @[computed_field]
  maxNewlineCount? : (τ : Type) → Doc τ → Option Nat
    | _, .failure =>
      none
    | _, .newline .. =>
      some 1
    | _, .text _
    | _, .flattened _ =>
      some 0
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .final d
    | _, .initial d
    | _, .free d
    | _, .unflattenable d
    | _, .guarded _ d
    | _, .costing _ d =>
      maxNewlineCount? _ d
    | _, .either a b =>
      .merge (max · ·) (maxNewlineCount? _ a) (maxNewlineCount? _ b)
    | _, .append a b =>
      .merge (· + ·) (maxNewlineCount? _ a) (maxNewlineCount? _ b)
  /-- Designates an approximation for whether a document is always empty. -/
  @[computed_field]
  alwaysEmptiness : (τ : Type) → Doc τ → Doc.AlwaysEmptiness
    | _, .failure =>
      .sometimesNonEmpty
    | _, .newline f =>
      if f.isEmpty then
        .alwaysEmptyIfFlattened
      else
        .sometimesNonEmpty
    | _, .text s =>
      if s.isEmpty then
        .alwaysEmpty
      else
        .sometimesNonEmpty
    | _, .flattened d =>
      match alwaysEmptiness _ d with
      | .alwaysEmpty => .alwaysEmpty
      | .alwaysEmptyIfFlattened => .alwaysEmpty
      | .sometimesNonEmpty => .sometimesNonEmpty
    | _, .unflattenable d =>
      match alwaysEmptiness _ d with
      | .alwaysEmpty => .alwaysEmpty
      | .alwaysEmptyIfFlattened => .sometimesNonEmpty
      | .sometimesNonEmpty => .sometimesNonEmpty
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .final d
    | _, .initial d
    | _, .free d
    | _, .guarded _ d
    | _, .costing _ d =>
      alwaysEmptiness _ d
    | _, .either a b =>
      -- A fully accurate implementation would have to account for `failure`,
      -- which is complicated by `final`.
      (alwaysEmptiness _ a).max (alwaysEmptiness _ b)
    | _, .append a b =>
      (alwaysEmptiness _ a).max (alwaysEmptiness _ b)
  /-- Designates an approximation for whether a document is always non-empty. -/
  @[computed_field]
  alwaysNonEmptiness : (τ : Type) → Doc τ → Doc.AlwaysNonEmptiness
    | _, .failure =>
      .sometimesEmpty
    | _, .newline f =>
      if f.isEmpty then
        .sometimesEmpty
      else
        .alwaysNonEmpty
    | _, .text s =>
      if s.isEmpty then
        .sometimesEmpty
      else
        .alwaysNonEmpty
    | _, .flattened d
    | _, .unflattenable d
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .final d
    | _, .initial d
    | _, .free d
    | _, .guarded _ d
    | _, .costing _ d =>
      alwaysNonEmptiness _ d
    | _, .either a b =>
      (alwaysNonEmptiness _ a).max (alwaysNonEmptiness _ b)
    | _, .append a b =>
      (alwaysNonEmptiness _ a).max (alwaysNonEmptiness _ b)
  @[computed_field]
  atomicness : (τ : Type) → Doc τ → Doc.Atomicness
    | _, .failure
    | _, .text .. =>
      .atomic
    | _, .newline .. =>
      .atomicIfFlattened
    | _, .flattened d =>
      match atomicness _ d with
      | .atomic => .atomic
      | .atomicIfFlattened => .atomic
      | .compoundAtomic => .compoundAtomic
      | .compoundAtomicIfFlattened => .compoundAtomic
      | .nonAtomic => .nonAtomic
    | _, .unflattenable d =>
      match atomicness _ d with
      | .atomic => .atomic
      | .atomicIfFlattened => .nonAtomic
      | .compoundAtomic => .compoundAtomic
      | .compoundAtomicIfFlattened => .nonAtomic
      | .nonAtomic => .nonAtomic
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .final d
    | _, .initial d
    | _, .free d
    | _, .guarded _ d
    | _, .costing _ d =>
      atomicness _ d
    | _, .either .. =>
      .nonAtomic
    | _, .append a b =>
      if alwaysEmptiness _ a matches .alwaysEmpty then
        atomicness _ b
      else if alwaysEmptiness _ b matches .alwaysEmpty then
        atomicness _ a
      else
        (atomicness _ a).max (atomicness _ b) |>.max .compoundAtomic
  /--
  Designates an underapproximation of the set of fullness states in which resolving the
  preprocessed document never fails, in any resolution context. For documents without `guarded`,
  this set is exact, i.e. the complement of `failureSet`.
  -/
  @[computed_field]
  neverFailsSet : (τ : Type) → Doc τ → FullnessStateSet
    | _, .failure =>
      0
    | _, .newline .. =>
      ~~~newlineFailureSet
    | _, .text s =>
      ~~~(textFailureSet s.isEmpty)
    -- Preprocessing can turn documents below `flattened` and `unflattenable` into `failure`.
    | _, .flattened _
    | _, .unflattenable _
    | _, .guarded _ _ =>
      0
    | _, .tagged _ d
    | _, .indented _ _ d
    | _, .aligned d
    | _, .unindented _ d
    | _, .free d
    | _, .costing _ d =>
      neverFailsSet _ d
    | _, .final d =>
      FullnessStateSet.finalAny (neverFailsSet _ d)
    | _, .initial d =>
      FullnessStateSet.initialAny (neverFailsSet _ d)
    | _, .either a b =>
      neverFailsSet _ a ||| neverFailsSet _ b
    | _, .append a b =>
      let neverFailsA := neverFailsSet _ a
      let neverFailsB := neverFailsSet _ b
      if neverFailsA == 0 || neverFailsB == 0 then
        0
      else
        FullnessStateSet.anySplit fun s1 s2 =>
          FullnessStateSet.contains neverFailsA s1 && FullnessStateSet.contains neverFailsB s2
deriving Inhabited, Repr

/--
Checks whether resolving the preprocessed document `d` in `fullness` fails in every resolution
context. For documents without `guarded`, this is exact.
-/
def Doc.isFailure (d : Doc τ) (fullness : FullnessState) : Bool :=
  FullnessStateSet.contains d.failureSet fullness

/--
Checks whether resolving the preprocessed document `d` in `fullness` never fails, in any resolution
context. For documents without `guarded`, this is exact.
-/
def Doc.neverFails (d : Doc τ) (fullness : FullnessState) : Bool :=
  FullnessStateSet.contains d.neverFailsSet fullness

/--
Checks whether the failure of resolving the preprocessed document `d` in `fullness` can depend on
the resolution context (the column position and the indentation), i.e. whether `fullness` is
neither in `Doc.failureSet` nor in `Doc.neverFailsSet`. Since both sets are exact for documents
without `guarded`, this is only possible below `guarded`. If this yields `false`, whether resolving
`d` fails only depends on `d` and `fullness`.

A document that never fails in a fullness state does not have context-dependent failure in it,
which stops the propagation to the ancestors of `guarded`: e.g. `either a b` does not have
context-dependent failure in the fullness states in which `b` never fails, even if `a` has
context-dependent failure there.
-/
def Doc.hasContextDependentFailure (d : Doc τ) (fullness : FullnessState) : Bool :=
  ! FullnessStateSet.contains (d.failureSet ||| d.neverFailsSet) fullness

/-- Checks whether `d` is guaranteed to be empty, i.e. equivalent to `.text ""`. -/
def Doc.isAlwaysEmpty (d : Doc τ) : Bool := d.alwaysEmptiness matches .alwaysEmpty

/-- Checks whether `d` is guaranteed to be non-empty, i.e. not equivalent to `.text ""`. -/
def Doc.isAlwaysNonEmpty (d : Doc τ) : Bool := d.alwaysNonEmptiness matches .alwaysNonEmpty

/--
Checks whether `d` is guaranteed to be compound-atomic, i.e. a sequence of text without newlines
and without choices.
-/
def Doc.isCompoundAtomic (d : Doc τ) : Bool :=
  d.atomicness matches .compoundAtomic || d.atomicness matches .atomic

/--
Checks whether `d` is guaranteed to be atomic, i.e. a node of text without newlines, choices
or `.append`s.
-/
def Doc.isAtomic (d : Doc τ) : Bool := d.atomicness matches .atomic

/--
Yields an empty document that serves as a neutral element for `Doc.append`.

Equivalent to `text ""`.
-/
def Doc.empty : Doc τ := .text ""

/--
Designates a document that either contains all newlines in an inner document or where all newlines
have been flattened.

The formatter will always choose a non-failing alternative if one is available or fail otherwise.
When both alternatives are not failing, it chooses an optimal rendering from both alternatives.

`maybeFlattened d` is equivalent to `either d (flattened d)`.

This construct corresponds to `group` in most traditional formatting languages.
-/
def Doc.maybeFlattened (d : Doc τ) : Doc τ := .either d d.flattened

/--
Designates a newline that is flattened to a single space when placed inside of a `flattened` node.

Equivalent to `newline " "`.
-/
def Doc.nl : Doc τ := .newline " "

/--
Designates a newline that is flattened to an empty string when placed inside of a `flattened` node.

Equivalent to `newline ""`.
-/
def Doc.break : Doc τ := .newline ""

/--
Designates a newline that cannot be flattened and will produce a `failure` node when attempting
to flatten it.

Equivalent to `unflattenable nl`.
-/
def Doc.hardNl : Doc τ := .unflattenable .nl

/--
Ensures that the level of indentation of an inner document is increased by 2 spaces after a newline.
Multiple `nested` nodes on the same line only increase the level of indentation once.

Examples:

```
nested
  (append
    (text "a")
    (append
      (text "b")
      (nested
        (append
          nl
          (text "c")))))
```
produces
```
ab
  c
```
---
```
nested
  (append
    (text "a")
    (append
      nl
      (append
        (text "b")
        (nested
          (append
            nl
            (text "c"))))))
```
produces
```
a
  b
    c
```
-/
def Doc.nested (d : Doc τ) : Doc τ := .indented 2 false d

/--
Increases the level of indentation of an inner document by 2 spaces after a newline.
Multiple `hardNested` nodes on the same line each increase the level of indentation by 2.

Example:

```
hardNested
  (append
    (text "a")
    (hardNested
      (append
        (append
          (text "b")
          nl)
        (text "c"))))
```
produces
```
ab
    c
```
-/
def Doc.hardNested (d : Doc τ) : Doc τ := .indented 2 true d

/--
Designates a document that can be rendered to one of several alternatives.

The formatter will always choose a non-failing alternative if one is available or fail otherwise.
When more than one alternative is not failing, it chooses an optimal rendering from
the non-failing alternatives.

Equivalent to `failure` if the set of alternatives is empty.
-/
def Doc.oneOf (ds : Array (Doc τ)) : Doc τ :=
  match ds[0]? with
  | none => .failure
  | some d => ds[1:].foldl (init := d) fun acc d => acc.either d

instance : Append (Doc τ) where
  append d1 d2 :=
    if d1.isAlwaysEmpty then
      d2
    else if d2.isAlwaysEmpty then
      d1
    else
      d1.append d2

/--
Appends multiple documents. Each document is appended to the last line of the preceding document.
-/
def Doc.join (ds : Array (Doc τ)) : Doc τ :=
  match ds[0]? with
  | none => .text ""
  | some d => ds[1:].foldl (init := d) fun acc d => acc ++ d

/-- Appends multiple documents with a separator document between each pair of adjacent documents. -/
def Doc.joinUsing (sep : Doc τ) (ds : Array (Doc τ)) : Doc τ :=
  match ds[0]? with
  | none => .text ""
  | some d => ds[1:].foldl (init := d) fun acc d => acc ++ sep ++ d

/-- Separator between two adjacent documents of a fill. -/
structure FillSep (α : Type) where
  /-- Separates the two documents when they are on the same line. -/
  flat : α
  /-- Precedes the newline when the two documents are on different lines. -/
  broken : α

/--
Appends multiple flattened documents with optional newlines between them. `sep i` is the separator
between `ds[i]` and `ds[i + 1]`.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillWith` will allow the document to split, but ensure that it is surrounded by newlines.
-/
def Doc.fillWith (ds : Array (Doc τ)) (sep : Nat → FillSep (Doc τ)) : Doc τ := Id.run do
  if ds.size == 0 then
    return .empty
  let hd := ds[0]!
  if ds.size == 1 then
    return hd
  let mut lastFlattened : Doc τ := .flattened hd
  let mut lastNotFlattened : Doc τ := hd
  for h : i in 1...ds.size do
    let d := ds[i]
    let { flat, broken } := sep (i - 1)
    let lastMaybeFlattened := .oneOf #[lastFlattened, lastNotFlattened]
    lastFlattened :=
      .oneOf #[
        .join #[lastFlattened, flat, .flattened d],
        .join #[lastMaybeFlattened, broken, .hardNl, .flattened d]
      ]
    lastNotFlattened := .join #[lastMaybeFlattened, broken, .hardNl, d]
  return .oneOf #[lastFlattened, lastNotFlattened]

def Doc.fill (ds : Array (Doc τ)) : Doc τ :=
  fillWith ds fun _ => { flat := .empty, broken := .empty }

/--
Appends multiple flattened documents with a separator document between each pair of adjacent
documents with optional newlines between them.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillUsing` will allow the document to split, but ensure that it is surrounded by newlines.
-/
def Doc.fillUsing (sep : Doc τ) (ds : Array (Doc τ)) : Doc τ :=
  fillWith ds fun _ => { flat := sep, broken := sep }

/--
Appends multiple flattened documents with either a space or a newline between each pair of adjacent
documents.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillUsingSpace` will allow the document to split, but ensure that it is surrounded by newlines.
Notably, as opposed to `Doc.fillUsing (Doc.text " ")`, it will not leave trailing spaces before
newlines.
-/
def Doc.fillUsingSpace (ds : Array (Doc τ)) : Doc τ :=
  fillWith ds fun _ => { flat := .text " ", broken := .empty }

/--
Appends multiple groups of flattened documents with either a space or a newline between each pair
of adjacent documents. `fillUsingSpaceWithSoftBoundaries` fills all documents of all groups exactly
like `Doc.fillUsingSpace` does.

Amongst the renderings that `Doc.fillUsingSpace` considers equally good, the formatter prefers the
ones that place a newline between two adjacent groups. The formatter charges `boundaryPenalty` for
every group boundary that it renders as a space. `boundaryPenalty` must thus be a cost that only
breaks ties between otherwise equally good renderings, for example
`DefaultCost.ofHeightFallbackPenalty 1`. This way, the formatter adds a newline at a group boundary
only if it does not increase the amount of lines.
-/
def Doc.fillUsingSpaceWithSoftBoundaries (boundaryPenalty : τ) (dss : Array (Array (Doc τ)))
    : Doc τ :=
  -- `isBoundary[i]` designates whether the separator in front of the `i`-th document is a group
  -- boundary.
  let isBoundary := dss.flatMap (·.mapIdx fun i _ => i == 0)
  let sep : Doc τ := .text " "
  let boundarySep : Doc τ := .costing boundaryPenalty sep
  fillWith dss.flatten fun i => {
    flat := if isBoundary[i + 1]! then boundarySep else sep
    broken := .empty
  }

/--
Appends multiple flattened documents with optional newlines between them, wrapping the entire
remainder of the document to the right of each separator or newline in `wrap`.
`sep i` designates the gap between `ds[i]` and `ds[i + 1]`: `some flat` separates both documents
with `flat` or a newline, while `none` separates them with `nl`.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillWrappingWith` will allow the document to split, but ensure that it is surrounded by newlines.
-/
def Doc.fillWrappingWith (ds : Array (Doc τ)) (wrap : Doc τ → Doc τ) (sep : Nat → Option (Doc τ))
    : Doc τ := Id.run do
  if ds.size == 0 then
    return .empty
  let last := ds.back!
  if ds.size == 1 then
    return last
  -- Since `wrap` encloses everything to the right of each separator or newline, the document is
  -- built right-to-left. `restFlattened` and `restNotFlattened` are the renderings of the suffix
  -- processed so far whose first document is flattened resp. not flattened.
  let mut restFlattened : Doc τ := .flattened last
  let mut restNotFlattened : Doc τ := last
  for (d, i) in ds.pop.zipIdx.reverse do
    let restMaybeFlattened := Doc.oneOf #[restFlattened, restNotFlattened]
    match sep i with
    | some flat =>
      let wrappedBrokenRest := wrap <| .join #[.hardNl, restMaybeFlattened]
      restFlattened :=
        .oneOf #[
          .join #[.flattened d, wrap <| .join #[flat, restFlattened]],
          .join #[.flattened d, wrappedBrokenRest]
        ]
      restNotFlattened := .join #[d, wrappedBrokenRest]
    | none =>
      -- `nl` rather than `hardNl` so that the whole document can still be flattened onto one line.
      let wrappedRest := wrap <| .join #[nl, restMaybeFlattened]
      restFlattened := .join #[.flattened d, wrappedRest]
      restNotFlattened := .join #[d, wrappedRest]
  return .oneOf #[restFlattened, restNotFlattened]

/--
Appends multiple flattened documents with optional newlines between them, wrapping the entire
remainder of the document to the right of each newline in `wrap`.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillWrapping` will allow the document to split, but ensure that it is surrounded by newlines.

For `wrap := Doc.nested`, this produces a staggered fill layout where each line is indented
further than the preceding one:

```
ab
  cd
    e
```
-/
def Doc.fillWrapping (ds : Array (Doc τ)) (wrap : Doc τ → Doc τ) : Doc τ :=
  fillWrappingWith ds wrap fun _ => some .empty

/--
Appends multiple flattened documents with either a space or a newline between each pair of adjacent
documents, wrapping the entire remainder of the document to the right of each space or newline in
`wrap`.
When a document can't be flattened or its flattened renderings exceed the column limit, then
`fillUsingSpaceWrapping` will allow the document to split, but ensure that it is surrounded by
newlines.

For `wrap := Doc.nested`, this produces a staggered fill layout where each line is indented
further than the preceding one:

```
a b
  c d
    e
```
-/
def Doc.fillUsingSpaceWrapping (ds : Array (Doc τ)) (wrap : Doc τ → Doc τ) : Doc τ :=
  fillWrappingWith ds wrap fun _ => some (.text " ")

structure Fillable (α : Type) where
  v : α
  allowFill : Bool
deriving Inhabited

def Doc.splitFillGroups (ds : Array (Fillable (Doc τ))) : Array (Array (Doc τ)) :=
  ds.toList.splitBy (fun { allowFill := allowFill1, .. } { allowFill := allowFill2, .. } =>
      allowFill1 && allowFill2)
    |>.map (·.toArray)
    |>.toArray
    |>.map fun group => group.map (·.1)

def Doc.fillSomeUsingSpace (ds : Array (Fillable (Doc τ))) : Doc τ := Id.run do
  let fillGroups := splitFillGroups ds
  joinUsing nl <| fillGroups.map fillUsingSpace

/--
Like `Doc.fillUsingSpaceWrapping`, but only fills adjacent documents that both allow filling;
all other pairs of adjacent documents are separated by a newline.
-/
def Doc.fillSomeUsingSpaceWrapping (ds : Array (Fillable (Doc τ))) (wrap : Doc τ → Doc τ) : Doc τ :=
  fillWrappingWith (ds.map (·.v)) wrap fun i =>
    if ds[i]!.allowFill && ds[i + 1]!.allowFill then some (.text " ") else none

/--
Provides pointer-based equality and hashing for a value of type `α`.
Ensures that the value for which the pointer is stored is kept alive as long as the pointer,
which guarantees that the pointer is not assigned to another (different object).

In the context of the caches of the formatter, this ensures that we do not get incorrect cache hits
with values that re-possessed the pointer of another value.
-/
structure PtrKey (α : Type u) where
  ptr : USize
  v : α
deriving Inhabited

unsafe def PtrKey.ofKey (v : α) : PtrKey α where
  ptr := ptrAddrUnsafe v
  v

instance : BEq (PtrKey α) where
  beq v1 v2 := v1.ptr == v2.ptr

instance : Hashable (PtrKey α) where
  hash v := hash v.ptr

public structure BEqCacheKey (τ : Type) where
  aPtr : PtrKey (Doc τ)
  bPtr : PtrKey (Doc τ)
deriving BEq, Hashable

public structure BEqState (τ : Type) [BEq τ] [Hashable τ] where
  cache : Std.HashMap (BEqCacheKey τ) Bool := {}

partial def Doc.beq [BEq τ] [Hashable τ] (a b : Doc τ) : Bool := goMemoized a b |>.run' {}
where
  goMemoized (a b : Doc τ) : StateM (BEqState τ) Bool := do
    let cacheKey := { aPtr := unsafe .ofKey a, bPtr := unsafe .ofKey b }
    if let some isBEq := (← get).cache.get? cacheKey then
      return isBEq
    let isBEq ← go a b
    modify fun s => { s with cache := s.cache.insert cacheKey isBEq }
    return isBEq
  go (a b : Doc τ) : StateM (BEqState τ) Bool := do
    match a, b with
    | .failure, .failure =>
      return true
    | .text sa, .text sb =>
      return sa == sb
    | .newline fa, .newline fb =>
      return fa == fb
    | .flattened da, .flattened db
    | .unflattenable da, .unflattenable db
    | .aligned da, .aligned db
    | .final da, .final db
    | .initial da, .initial db
    | .free da, .free db =>
      goMemoized da db
    | .unindented onca da, .unindented oncb db =>
      if onca != oncb then
        return false
      goMemoized da db
    | .tagged ida da, .tagged idb db =>
      if ida != idb then
        return false
      goMemoized da db
    | .indented na ca da, .indented nb cb db =>
      if na != nb || ca != cb then
        return false
      goMemoized da db
    | .guarded pa da, .guarded pb db =>
      if pa.id != pb.id then
        return false
      goMemoized da db
    | .costing ca da, .costing cb db =>
      if ca != cb then
        return false
      goMemoized da db
    | .either da1 da2, .either db1 db2
    | .append da1 da2, .append db1 db2 =>
      if !(← goMemoized da1 db1) then
        return false
      goMemoized da2 db2
    | _, _ =>
      return false

public instance [BEq τ] [Hashable τ] : BEq (Doc τ) where
  beq a b := a.beq b
