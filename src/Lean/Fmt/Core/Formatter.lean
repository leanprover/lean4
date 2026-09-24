/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Fmt.Core.Basic
public import Lean.Fmt.Util.Basic
public import Std.Data.HashSet.Basic
import Std.Data.HashSet.Iterator
import Std.Data.Iterators.Consumers.Set
import Init.Data.Iterators.Combinators.FilterMap
import Init.Data.String.Search

/-!
`Fmt` formatter.

This file implements the formatter of 'A Pretty Expressive Printer' [1] by
Sorawee Porncharoenwase, Justin Pombrio and Emina Torlak.
This implementation is based on the Racket implementation of pretty-expressive [2].

[1] https://arxiv.org/pdf/2310.01530
[2] https://docs.racket-lang.org/pretty-expressive/
-/

namespace Lean.Fmt

open _root_.Std

structure PreprocessingCacheKey (τ : Type) where
  docPtr : PtrKey (Doc τ)
  isFlattened : Bool
deriving BEq, Hashable

structure PreprocessingState (τ : Type) [BEq τ] [Hashable τ] where
  cache : HashMap (PreprocessingCacheKey τ) (Doc τ) := {}

/--
Erases all `flattened` and `unflattenable` nodes from a document by flattening all newlines within
each `flattened` node and replacing each `unflattenable` node within a `flattened` node
with `failure`.

The important property we require of `preprocess` is that it does not destroy the sharing in the
input document: a document of shared size n must still be of shared size O(n) after preprocessing.
This ensures that preprocessed documents can still be formatted asymptotically as quickly as the
input document.

Notably, preprocessing `flattened` nodes does not destroy the sharing of the input document, as
each document occurs at most in its flattened or non-flattened form, and so each document is
duplicated at most once.

Eliminating `indented`, `aligned` and `unaligned` nodes by computing the indentation level of each
leaf node and then reducing `newline` nodes to an unindented `newline` node and some text
representing the current level of indentation is not possible for this reason,
as each document can occur in arbitrarily many indentation contexts, and so the sharing of the
input document would be destroyed.

The Racket implementation skips this step by implementing a global preprocessing cache
and implementing `flattened` as a function that flattens the newlines in the inner document.
We instead implement this as a separate preprocessing step to circumvent the global
preprocessing cache.
-/
partial def Doc.preprocess [BEq τ] [Hashable τ] (d : Doc τ) : Doc τ := goMemoized d false |>.run' {}
where
  goMemoized (d : Doc τ) (isFlattened : Bool) : StateM (PreprocessingState τ) (Doc τ) := do
    let cacheKey := { docPtr := unsafe .ofKey d, isFlattened }
    -- Re-using cached preprocessing results is essential for not destroying the
    -- shared structure of the input document.
    if let some d' := (← get).cache.get? cacheKey then
      return d'
    let d' ← go d isFlattened
    modify fun s => { s with cache := s.cache.insert cacheKey d' }
    return d'
  go (d : Doc τ) (isFlattened : Bool) : StateM (PreprocessingState τ) (Doc τ) := do
    match d with
    | .newline f =>
      if isFlattened then
        return .text f
      else
        return .newline f
    | .unflattenable d =>
      if isFlattened then
        return .failure
      else
        goMemoized d false
    | .flattened d =>
      goMemoized d true
    | .failure =>
      return d
    | .text s =>
      let lines := s.split '\n' |>.map (Doc.text ·.toString) |>.toArray
      if lines.size == 1 then
        return .text s
      else if isFlattened then
        return .failure
      else
        return .joinUsing .nl lines
    | .tagged id d =>
      let d ← goMemoized d isFlattened
      return .tagged id d
    | .indented n c d =>
      let d ← goMemoized d isFlattened
      return .indented n c d
    | .aligned d =>
      let d ← goMemoized d isFlattened
      return .aligned d
    | .unindented onlyNonCumulative d =>
      let d ← goMemoized d isFlattened
      return .unindented onlyNonCumulative d
    | .final d =>
      let d ← goMemoized d isFlattened
      return .final d
    | .initial d =>
      let d ← goMemoized d isFlattened
      return .initial d
    | .free d =>
      let d ← goMemoized d isFlattened
      return .free d
    | .guarded p d =>
      let d ← goMemoized d isFlattened
      return .guarded p d
    | .costing c d =>
      let d ← goMemoized d isFlattened
      return .costing c d
    | .either d1 d2 =>
      let d1 ← goMemoized d1 isFlattened
      let d2 ← goMemoized d2 isFlattened
      return .either d1 d2
    | .append d1 d2 =>
      let d1 ← goMemoized d1 isFlattened
      let d2 ← goMemoized d2 isFlattened
      return .append d1 d2

/--
Cost function that the formatter is invoked with.

Must satisfy the laws documented in `LawfulCost`.
-/
public class Cost (τ : Type) [Add τ] [LE τ] where
  /-- Cost of inserting a text of `length` at `columnPos`. -/
  textCost : (columnPos length : Nat) → τ
  /-- Cost of inserting a newline with `indentationAfterNewline`. -/
  newlineCost : (indentationAfterNewline : Nat) → τ
  /--
  Maximum width after which the formatter stops trying to find an optimal rendering
  according to the cost function and instead reverts to simpler heuristics to choose a rendering.
  This value should be chosen to be larger than the actual column limit so that the formatter
  can produce optimal renderings even when all renderings exceed the column limit.
  -/
  optimalityCutoffWidth : Nat

structure InternalOutput where
  rendering : String
  tags : Std.TreeMap TagId (Std.HashSet (String.Pos.Raw × String.Pos.Raw))
deriving Inhabited

public structure Output where
  rendering : String
  tags : Std.TreeMap TagId (Std.HashSet rendering.toSlice.Subslice)
deriving Inhabited

def Output.ofInternalOutput! (o : InternalOutput) : Output where
  rendering := o.rendering
  tags := Id.run do
    let mut r : Std.TreeMap TagId (Std.HashSet o.rendering.toSlice.Subslice) := ∅
    for (id, ranges) in o.tags do
      let subslices :=
        ranges.iter.map fun (startPos, endPos) =>
          let startPos := o.rendering.toSlice.pos! startPos
          let endPos := o.rendering.toSlice.pos! endPos
          if h : startPos ≤ endPos then
            ⟨startPos, endPos, h⟩
          else
            panic! "Output.ofInternalOutput!: Got `startPos > endPos`."
      r := r.insert id subslices.toHashSet
    return r

/--
A measure is a tuple of the compound cost of a specific rendering and a writer monad to produce the
rendering.

The compound cost of a measure consists of both a configurable cost (as defined by a configurable
cost function, plus explicit costs added by `Doc.costing` nodes) and the current length of the last
line of the rendering.
A measure is considered to be cheaper than (or to dominate) another measure if both the configurable
cost as determined by the cost function and the last length of the line are smaller than that of
the other measure. In the formatter, we prune measures if they are dominated by another measure.

For a lawful cost function, the configurable cost of a measure increases with more lines and
as lines get longer, i.e. it increases as documents are appended to it.
This means that we cannot simply prune measures using the configurable cost alone:
a measure might have a lower configurable cost than another measure for the time being, but when we
append to both measures, the second measure might suddenly become more expensive than the first one.

With the default cost function, this occurs if e.g. both renderings have the same amount of lines,
all of which are below the column limit, while the second rendering is close to the column limit on
the last line. Appending lots of text to the last line of both renderings will then cause the cost
of the second measure to balloon relative to that of the first one.

Notably, this kind of future divergence in cost between the two measures is limited to the last line
of the rendering, as we will always append the exact same documents to both of them and their column
positions will be synced when a newline is inserted. Additionally, lawful cost functions have the
property that inserting text at a smaller column position (i.e. at the end of a shorter last line)
will always be cheaper than inserting text at a larger column position, and so a compound cost that
is smaller both w.r.t. the configurable cost and the last line length than another compound cost
will also remain smaller than the other cost in the future when we append documents to the last
line, which means that we can safely prune the dominated measure.

In summary, for a lawful cost function, it is both necessary and sufficient to include the length of
the last line as a separate parameter in the compound cost and only prune measures that dominate
other measures:
- It is necessary because not including it can cause us to prune measures that will become cheaper
  than other measures in the future
- It is sufficient because the future divergence in cost for a lawful cost function is limited to
  the last line of the rendering, and for lawful cost functions inserting text at a smaller
  column position (i.e. at the end of a shorter last line) will always be cheaper than inserting
  at a larger column position.

Finally, the inclusion of the last line length in the compound cost bounds the time complexity of
the formatter by bounding the maximum size of the sets of measures it processes:
Each cost function comes with an optimality cutoff width `W`, after which the formatter will stop
attempting to compute optimal measures according to the configurable cost and simply pick just one
heuristically. Hence, all measures in a set of measures that do not exceed `W` have a
last line length of at most `W`.
When sets of measures are combined by the formatter, it prunes dominated measures to retain the
invariant that sets of measures contain no dominated measures.
Together, this means that each set of measures in the formatter can only contain at most `W`
measures that don't dominate one another: if there were more than `W` measures, at least two
measures `m₁` and `m₂` must have the same last line length, which, by the totality of `≤` of
a lawful cost function, means that either `m₁` dominates `m₂`, or `m₂` dominates `m₁`.
-/
structure Measure (τ : Type) where
  /-- Length of the last line of the rendering represented by this measure. -/
  lastLineLength : Nat
  /--
  Configurable cost of the rendering represented by this measure, as defined by the cost function,
  plus explicit costs added by `Doc.costing` nodes.
  -/
  cost : τ
  /--
  Whether after having resolved this measure, the non-cumulative indentation that it was resolved
  with is still pending.
  Set to `false` after a newline.
  -/
  hasPendingNonCumulativeIndentation : Bool
  /--
  Writer monad that produces the rendering that this measure presents with a set of associated tags.
  -/
  output : StateM InternalOutput Unit

variable {τ : Type} [BEq τ] [Hashable τ] [Zero τ] [Add τ] [LE τ] [DecidableLE τ] [Cost τ]

/--
Whether a measure subsumes another measure. See the documentation of `Measure` for details on
what measure domination entails.

The `hasPendingNonCumulativeIndentation` clause encodes that, at otherwise-equal cost and last
line length, a measure with pending non-cumulative indentation is preferable to one without:
when resolving a document appended to such a measure, the cumulative *and* the non-cumulative
indentation in the surrounding context are both retained, so a non-cumulative `indented` further
to the right may shadow it (potentially producing less indentation than the materialized
alternative). A measure without pending non-cumulative indentation has already folded that
indentation into its cumulative level and so unconditionally increases future column positions.
-/
def Measure.dominates (m1 m2 : Measure τ) : Bool :=
  m1.lastLineLength <= m2.lastLineLength && m1.cost <= m2.cost
    && (m1.hasPendingNonCumulativeIndentation || !m2.hasPendingNonCumulativeIndentation)

/-- Determines the measure that represents the concatenation of the renderings of two measures. -/
def Measure.append (m1 m2 : Measure τ) : Measure τ where
  lastLineLength := m2.lastLineLength
  cost := m1.cost + m2.cost
  hasPendingNonCumulativeIndentation := m2.hasPendingNonCumulativeIndentation
  output := do
    m1.output
    m2.output

/-- Sets whether this measure has pending non-cumulative indentation. -/
def Measure.setHasPendingNonCumulativeIndentation (m : Measure τ) (nonCumulativeIndentation : Nat)
    : Measure τ := {
  m with
  hasPendingNonCumulativeIndentation := nonCumulativeIndentation > 0
}

/-- Adds a tag to the rendering presented by this measure. -/
def Measure.addTag (m : Measure τ) (tag : TagId) : Measure τ := {
  m with
  output := do
    let tagStartPos := (← get).rendering.rawEndPos
    m.output
    let tagEndPos := (← get).rendering.rawEndPos
    modify fun out =>
      let tagRange := (tagStartPos, tagEndPos)
      {
        out with
        tags :=
          out.tags.alter tag fun
            | none => some {tagRange}
            | some ranges => some <| ranges.insert tagRange
      }
}

/--
Determines the measure for a `Doc.free` document from the measure of its inner document, which was
resolved at `columnPos`. Retains the rendering of the inner document, but discards its cost and
resets the last line length to `columnPos`, so that the surrounding document is resolved as if the
rendering of the inner document was empty.
-/
def Measure.makeFreeAt (m : Measure τ) (columnPos : Nat) : Measure τ := {
  m with
  lastLineLength := columnPos
  cost := 0
}

/-- Adds a cost to the cost of this measure. -/
def Measure.addCost (m : Measure τ) (c : τ) : Measure τ := { m with cost := m.cost + c }

/--
Runs the writer monad of a measure, printing its rendering to a string and collecting the
set of tags for the rendering.
-/
def Measure.print (m : Measure τ) : Output :=
  let (_, output) := m.output.run { rendering := "", tags := ∅ }
  .ofInternalOutput! output

/--
A tainted measure is a measure for a rendering that exceeds the optimality cutoff width of the
cost function passed to the formatter.

Notably, it does not possess a compound cost that we maintain, but merely a series of steps that
describe how to resolve the tainted measure to a single measure, as well as an approximation of the
amount of newlines in the rendering of the tainted measure.

The formatter will always prune tainted measures in favor of non-tainted measures.
When the formatter has to choose amongst multiple tainted measures, instead of tracking all of them
using a cost function like for non-tainted measures, it simply picks the tainted measure with the
largest approximation for the amount of newlines, so as to attempt to heuristically produce
renderings that are higher (in terms of amount of lines) instead of ones where all text is
squished into the same line.

Tainting measures instead of attempting to determine an optimal one amongst multiple tainted
measures bounds the time complexity of the formatter, as described in the documentation
of `Measure`.

Compared to the Racket implementation of pretty-expressive, `TaintedMeasure` is a defunctionalized
implementation of the tainted measures in the Racket implementation, which implements them using
promises that lazily resolve a tainted measure to a regular measure after the measure resolution
loop is complete. This implementation using promises violates the positivity constraints of
inductive types, as the lazy measure resolution would itself maintain a memoization cache that
can contain tainted measures. Defunctionalization ensures that we limit the set of potential
lazy resolutions to a finite set of (sound) options, which makes the type satisfy the positivity
constraint.
-/
inductive TaintedMeasure (τ : Type) where
  /--
  Merge two tainted measures. Resolving this tainted measure amounts to resolving the first measure
  and only resolving the second measure if the resolution of the first tainted measure failed.

  Resolving the first measure can only fail if it contains a document with context-dependent
  failure (see `Doc.hasContextDependentFailure`), since the resolver prunes all other failing
  documents before it creates tainted measures for them. Such documents only occur below
  `Doc.guarded`, and the second measure is only resolved for them.
  -/
  | mergeTainted (tm1 tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  /--
  Append a document to the rendering of a tainted measure. Resolving this tainted measure amounts to
  resolving the tainted measure on the left, resolving the document on the right in the column
  position after resolving the tainted measure on the left and with the given
  context, picking a measure from the set of measures of the resolution on the right
  and then appending those.
  -/
  | taintedAppend
    (tm1 : TaintedMeasure τ) (d2 : Doc τ) (indentation nonCumulativeIndentation : Nat)
    (fullness : FullnessState) (maxNewlineCount? : Option Nat)
  /--
  Append a tainted measure to a regular measure. Resolving this tainted measure amounts to simply
  resolving the tainted measure on the right and appending it to the measure on the left.
  -/
  | appendTainted (m1 : Measure τ) (tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  /--
  Sets whether a tainted measure has pending non-cumulative indentation.
  Resolving this tainted measure amounts to resolving the inner tainted measure and adjusting the
  resulting `hasPendingNonCumulativeIndentation` flag.
  -/
  | setTaintedHasPendingNonCumulativeIndentation
    (tm : TaintedMeasure τ) (pendingNonCumulativeIndentation : Nat) (maxNewlineCount? : Option Nat)
  /--
  Add a tag to the tainted measure. Resolving this tainted measure amounts to resolving the inner
  tainted measure and adding the tag to the resulting measure.
  -/
  | addTag (tm : TaintedMeasure τ) (tag : TagId) (maxNewlineCount? : Option Nat)
  /--
  Add a cost to the tainted measure. Resolving this tainted measure amounts to resolving the inner
  tainted measure and adding the cost to the resulting measure.
  -/
  | addCost (tm : TaintedMeasure τ) (c : τ) (maxNewlineCount? : Option Nat)
  /--
  Resolve a tainted measure for a given resolution context to a regular measure.
  Amounts to resolving the given document in the given context, picking a measure from the set of
  measures produced by the resolution and memoizing whether the resolution failed so that
  no failed resolution of a tainted measure is tried twice in the same fullness state and the time
  complexity for tainted measure resolution remains bounded by `16*amount of documents`.

  Notably, the resolution of the document in the given context skips the taintedness-check for the
  top level node, so this will process the top-level node of the document and then recurse with
  potentially tainted child documents until eventually the full tainted measure is resolved.
  -/
  | resolveTainted
    (d : Doc τ) (columnPos : Nat) (indentation nonCumulativeIndentation : Nat)
    (fullness : FullnessState) (maxNewlineCount? : Option Nat)
deriving Inhabited

/-- Approximation for the maximum amount of newlines in the rendering of a tainted measure. -/
def TaintedMeasure.maxNewlineCount? : TaintedMeasure τ → Option Nat
  | .mergeTainted (maxNewlineCount? := n) .. => n
  | .taintedAppend (maxNewlineCount? := n) .. => n
  | .appendTainted (maxNewlineCount? := n) .. => n
  | .setTaintedHasPendingNonCumulativeIndentation (maxNewlineCount? := n) .. => n
  | .addTag (maxNewlineCount? := n) .. => n
  | .addCost (maxNewlineCount? := n) .. => n
  | .resolveTainted (maxNewlineCount? := n) .. => n

/--
Yields a `TaintedMeasure.mergeTainted` where the tainted measure with a larger newline approximation
is resolved first.

Yields just the measure with a larger newline approximation if `prunable` is set to `true`, which
should only be set if it can be guaranteed that both tainted measures will always fail at the same
time (in which case we never need to try both).
-/
def TaintedMeasure.merge (tm1 tm2 : TaintedMeasure τ) (prunable : Bool) : TaintedMeasure τ :=
  let (tm1, tm2) :=
    if Option.le (· <= ·) tm2.maxNewlineCount? tm1.maxNewlineCount? then
      (tm1, tm2)
    else
      (tm2, tm1)
  if prunable then
    tm1
  else
    -- There are two reasonable options for this newline approximation:
    -- 1. The newline approximation of the first measure (as used by the Racket implementation)
    -- 2. The maximum of both newline approximations
    -- The first option is more accurate if resolving `tm1` does not fail, in which case the second
    -- option is a worse approximation, while the second option is more accurate if resolving
    -- `tm1` can fail.
    .mergeTainted tm1 tm2 tm1.maxNewlineCount?

/--
Set of non-tainted measures.

Fulfills the following invariants:
1. No two measures dominate each other.
2. The set is sorted by last line length (descending), with measures with
   `hasPendingNonCumulativeIndentation = true` preceding those with
   `hasPendingNonCumulativeIndentation = false` at ties in last line length.

Two measures sharing a last line length and `hasPendingNonCumulativeIndentation` would be
totally ordered by cost (by totality of `≤` on `τ`) and hence one would dominate the other,
violating invariant 1. So each last line length holds at most two measures (one per flag value),
and within each `hasPendingNonCumulativeIndentation`-sublist the set is sorted by cost (strictly
ascending).

Since all of these measures are non-tainted, both invariants imply that there are at most `2*W`
measures in a given set of non-tainted measures, where `W` is the optimality cutoff width of the
cost function.
-/
abbrev MeasureSet.Set (τ : Type) := List (Measure τ)

/--
Skyline-merges two sublists of measures that all share the same
`hasPendingNonCumulativeIndentation`. Both inputs are expected to be sorted by `lastLineLength`
descending; the output is sorted by `lastLineLength` descending with strictly ascending cost.

The amortized monotonic-stack `push` keeps the running result in reverse (head = most recently
pushed = smallest `lastLineLength`) so that pops are `O(1)`.

Tolerates inputs with internal dominations: the merge is also used as a single-list cleanup
(with the other side `[]`), where `Measure.append` may have introduced cost plateaus under
non-strictly-monotone `+`.
-/
partial def MeasureSet.Set.mergeSamePending (s1 s2 : List (Measure τ)) : List (Measure τ) :=
  go s1 s2 [] |>.reverse
where
  -- Within a same-pending sublist, `m.lastLineLength ≤ top.lastLineLength` holds by the push
  -- order, so `m.dominates top` reduces to `m.cost ≤ top.cost`, and (in the second branch)
  -- `top.dominates m` reduces to `top.lastLineLength = m.lastLineLength`.
  --
  -- At an exact tie (mutual domination), the order of the two checks decides which measure
  -- survives: checking `top.dominates m` first keeps the incumbent. Through the merge order of
  -- `analyzeAppend`, this resolves equal-cost ties in favor of renderings that break later in
  -- the text rather than earlier.
  push (acc : List (Measure τ)) (m : Measure τ) : List (Measure τ) :=
    match acc with
    | [] =>
      [m]
    | top :: rest =>
      if top.dominates m then
        acc
      else if m.dominates top then
        push rest m
      else
        m :: acc
  go : List (Measure τ) → List (Measure τ) → List (Measure τ) → List (Measure τ)
    | [], ms, acc =>
      ms.foldl push acc
    | ms, [], acc =>
      ms.foldl push acc
    | m1 :: ms1', m2 :: ms2', acc =>
      if m1.lastLineLength >= m2.lastLineLength then
        go ms1' (m2 :: ms2') (push acc m1)
      else
        go (m1 :: ms1') ms2' (push acc m2)

/--
Interleaves a T-pending sublist `ts` and an F-pending sublist `fs` into one list sorted by
`lastLineLength` descending, T preceding F at ties, dropping F-elements dominated by some
T-element along the way. Both inputs are sorted by `lastLineLength` descending with strictly
ascending cost.

The only cross-pending domination direction is `T` dominating `F` (the third clause of
`dominates` forbids the converse), and within `ts` the cost strictly ascends as
`lastLineLength` descends, so the minimum-cost candidate dominator for any `f` is exactly
`ts.head` once `ts.head.lastLineLength ≤ f.lastLineLength`. The prune therefore folds into the
merge step at no extra cost.
-/
partial def MeasureSet.Set.combineAndPrune (ts fs : List (Measure τ)) : List (Measure τ) :=
  match ts, fs with
  | [], _ =>
    fs
  | _, [] =>
    ts
  | t :: ts', f :: fs' =>
    if t.dominates f then
      if t.lastLineLength = f.lastLineLength then
        -- Tie: emit `t` (T-first), drop `f`.
        t :: combineAndPrune ts' fs'
      else
        -- `t.lastLineLength < f.lastLineLength`: drop `f`; `t` may still dominate later
        -- F-elements, so don't advance past `t` yet.
        combineAndPrune ts fs'
    else if t.lastLineLength >= f.lastLineLength then
      t :: combineAndPrune ts' (f :: fs')
    else
      f :: combineAndPrune ts fs'

/--
Merges two sets of non-tainted measures, maintaining their invariants in the result.

The set invariants decompose along `hasPendingNonCumulativeIndentation`:
* Within each pending value, a no-dom set is exactly a 2-D skyline (sorted by `lastLineLength`
  desc with strictly ascending cost). `mergeSamePending` merges two such skylines in linear
  time.
* Across pending values, only `T` can dominate `F` (the third clause of `dominates`); `F`
  cannot dominate `T`. `combineAndPrune` interleaves the two skylines by `lastLineLength` desc
  (T-first at ties) and drops F-elements dominated by a T-element in the same linear pass.
Total time: `O(|ms1| + |ms2|)`.
-/
def MeasureSet.Set.merge (ms1 ms2 : MeasureSet.Set τ) : MeasureSet.Set τ :=
  let (ts1, fs1) := ms1.partition (·.hasPendingNonCumulativeIndentation)
  let (ts2, fs2) := ms2.partition (·.hasPendingNonCumulativeIndentation)
  combineAndPrune (mergeSamePending ts1 ts2) (mergeSamePending fs1 fs2)

/--
Cleans up an already-sorted list of measures (sorted by `lastLineLength` desc, T-pending
preceding F-pending at ties) into a valid measure set, dropping internal dominations.

Useful after `Measure.append` shifts costs by a fixed amount — under non-strictly-monotone `+`
distinct costs may collapse to equal cost, introducing dominations both within a same-pending
sublist (later, smaller-`lastLineLength` measures dominating earlier ones) and across pending
(T newly dominating F at smaller-or-equal `lastLineLength`).
Time: `O(|ms|)`.
-/
def MeasureSet.Set.dedup (ms : MeasureSet.Set τ) : MeasureSet.Set τ := ms.merge []

/--
A set of measures is either a single tainted measure or a set of non-tainted measures.
The formatter prefers non-empty sets of measures over tainted measures and tainted measures
over empty sets of measures.
-/
inductive MeasureSet (τ : Type) where
  | tainted (tm : TaintedMeasure τ)
  | set (ms : MeasureSet.Set τ)
deriving Inhabited

/--
Merges two sets of measures, preferring non-empty sets of measures over tainted measures and tainted
measures over empty sets of measures.
Tainted measures are merged according to `TaintedMeasure.merge` and sets of non-tainted measures
are merged according to `MeasureSet.Set.merge`.

`prunable` can only be set to `true` if either `ms1` and `ms2` are not both tainted, or if it can be
guaranteed that both tainted measures will always fail at the same time
(in which case we never need to try both).
-/
def MeasureSet.merge (ms1 ms2 : MeasureSet τ) (prunable : Bool) : MeasureSet τ :=
  match ms1, ms2 with
  | _, .set [] =>
    ms1
  | .set [], _ =>
    ms2
  | .tainted tm1, .tainted tm2 =>
    .tainted (tm1.merge tm2 prunable)
  | _, .tainted _ =>
    ms1
  | .tainted _, _ =>
    ms2
  | .set ms1, .set ms2 =>
    .set (ms1.merge ms2)

/--
Adjusts all non-cumulative indentations in a set of measures according to
`Measure.setHasPendingNonCumulativeIndentation` and
`TaintedMeasure.setTaintedHasPendingNonCumulativeIndentation`.
-/
def MeasureSet.setHasPendingNonCumulativeIndentation
    (m : MeasureSet τ) (pendingNonCumulativeIndentation : Nat)
    : MeasureSet τ :=
  match m with
  | .set ms =>
    .set <| .dedup <|
      ms.map (·.setHasPendingNonCumulativeIndentation pendingNonCumulativeIndentation)
  | .tainted tm =>
    .tainted (.setTaintedHasPendingNonCumulativeIndentation tm pendingNonCumulativeIndentation
      tm.maxNewlineCount?)

/--
Adds a tag to all measures in a set of measures according to `Measure.addTag` and
`TaintedMeasure.addTag`.
-/
def MeasureSet.addTag (m : MeasureSet τ) (tag : TagId) : MeasureSet τ :=
  match m with
  | .set ms => .set <| ms.map (·.addTag tag)
  | .tainted tm => .tainted <| .addTag tm tag tm.maxNewlineCount?

/--
Adds a cost to all measures in a set of measures according to `Measure.addCost` and
`TaintedMeasure.addCost`.
-/
def MeasureSet.addCost (m : MeasureSet τ) (c : τ) : MeasureSet τ :=
  match m with
  | .set ms => .set <| .dedup <| ms.map (·.addCost c)
  | .tainted tm => .tainted <| .addCost tm c tm.maxNewlineCount?

/--
Memoization key for sets of measures produced by the formatter.
Includes the full context that uniquely determines a set of measures:
- A pointer to the document that is being formatted
- The column position at which the document is being formatted
- The current level of indentation within which the document is being formatted
- The current level of non-cumulative indentation within which the document is being formatted
- The fullness state surrounding the document
-/
structure SetCacheKey (τ : Type) where
  docPtr : PtrKey (Doc τ)
  columnPos : Nat
  indentation : Nat
  nonCumulativeIndentation : Nat
  fullness : FullnessState
deriving BEq, Hashable

/--
State of the resolver and the resolver for tainted measures, which usually runs after the regular
resolver, but is also invoked during resolution by `Doc.free` nodes.

Maintains two separate memoization caches:
- `setCache`, which memoizes sets of measures that are produced during resolution per `SetCacheKey`.
  This is the main memoization cache of the formatter. It memoizes all resolution results for
  resolution contexts that do not exceed the optimality cutoff width and ensures that the time
  complexity of resolution remains reasonable.
  The `setCache` is re-used in resolutions performed by the resolution of tainted measures, which
  usually runs after resolution, but is also invoked during resolution by `Doc.free` nodes.
  Notably, in the resolution of tainted measures, it is not used for resolving the
  top-level measure in a `TaintedMeasure.resolveTainted`, as this would simply again yield a
  tainted measure, and no progress in resolving the tainted measure would be made.
  In the Racket implementation, this cache is replaced by several mutable caches
  (one per fullness state) on the document.
- `resolvedTaintedCache`, which memoizes the measure (if any) produced by resolving a tainted
  measure. Tainted measures can be shared during resolution if they are cached in `setCache` and
  then later re-used. This cache ensures that the resolver for tainted measures does not perform
  additional work relative to the resolver if the resolver has already figured out that two tainted
  measures are identical.
  In the Racket implementation, this cache is replaced with mutable state on the tainted measure.

The Racket implementation additionally memoizes whether resolving a document failed. Here, whether
a document fails is instead determined in advance by `Doc.failureSet`, which is exact for documents
without `guarded`.
-/
structure ResolutionState (τ : Type) [BEq τ] [Hashable τ] where
  setCache : HashMap (SetCacheKey τ) (MeasureSet τ) := {}
  resolvedTaintedCache : HashMap (PtrKey (TaintedMeasure τ)) (Option (Measure τ)) := {}

/--
Monad for resolving a document in a resolution context to a set of measures.
Uses `StateRefT` to avoid having to box the state together with return values during resolution.
-/
abbrev ResolverM (σ τ : Type) [BEq τ] [Hashable τ] := StateRefT (ResolutionState τ) (ST σ)

def ResolverM.run (f : ResolverM σ τ α) : ST σ α := f.run' {}

@[inline]
def getCachedSet?
    (d : Doc τ) (columnPos indentation nonCumulativeIndentation : Nat) (fullness : FullnessState)
    : ResolverM σ τ (Option (MeasureSet τ)) := do
  return (← get).setCache.get? {
    docPtr := unsafe .ofKey d
    columnPos
    indentation
    nonCumulativeIndentation
    fullness
  }

@[inline]
def setCachedSet
    (d : Doc τ) (columnPos indentation nonCumulativeIndentation : Nat) (fullness : FullnessState)
    (set : MeasureSet τ)
    : ResolverM σ τ Unit :=
  modify fun state => {
    state with
    setCache :=
      state.setCache.insert
        { docPtr := unsafe .ofKey d, columnPos, indentation, nonCumulativeIndentation, fullness }
        set
  }

inductive CacheResult (α : Type) where
  | miss
  | hit (cached : α)

@[inline]
def getCachedResolvedTainted? (tm : TaintedMeasure τ)
    : ResolverM σ τ (CacheResult (Option (Measure τ))) := do
  match (← get).resolvedTaintedCache.get? (unsafe .ofKey tm) with
  | none => return .miss
  | some cached? => return .hit cached?

@[inline]
def setCachedResolvedTainted (tm : TaintedMeasure τ) (m? : Option (Measure τ))
    : ResolverM σ τ Unit :=
  modify fun state => {
    state with
    resolvedTaintedCache := state.resolvedTaintedCache.insert (unsafe .ofKey tm) m?
  }

def Resolver (σ τ : Type) [BEq τ] [Hashable τ] :=
  (d : Doc τ) → (columnPos indentation nonCumulativeIndentation : Nat) → (fullness : FullnessState)
    → ResolverM σ τ (MeasureSet τ)

def TaintedResolver (σ τ : Type) [BEq τ] [Hashable τ] :=
  (tm : TaintedMeasure τ) → ResolverM σ τ (Option (Measure τ))

/--
Checks whether we have a memoized result for a given resolution context and if so, uses that.
Otherwise, `f` is evaluated and the result is memoized, unless the column position or the level of
indentation exceeds the optimality cutoff width.
-/
@[specialize]
def Resolver.memoize (f : Resolver σ τ)
    : Resolver σ τ := fun d columnPos indentation nonCumulativeIndentation fullness => do
  if d.isFailure fullness then
    return .set []
  if columnPos > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ then
    return ← f d columnPos indentation nonCumulativeIndentation fullness
  if let some cachedSet ← getCachedSet? d columnPos indentation nonCumulativeIndentation fullness
  then
    return cachedSet
  let r ← f d columnPos indentation nonCumulativeIndentation fullness
  setCachedSet d columnPos indentation nonCumulativeIndentation fullness r
  return r

public inductive FormattingError
  | tainted
  | failure
deriving Inhabited

mutual

/--
Determines the set of measures for a given resolution context.
The root node is not memoized, while nodes below the root node can be memoized.

Notably, this function skips checks that determine whether the context at the root node already
exceeds the optimality cutoff width, which (together with not memoizing the root node) means that
we can use this function to resolve tainted documents to non-tainted ones in the resolver for
tainted measures.
-/
partial def MeasureSet.resolveCore
    : Resolver σ τ := fun d columnPos indentation nonCumulativeIndentation fullness => do
  match d with
  | .failure =>
    return .set []
  | .newline .. =>
    let lineIndentation := indentation + nonCumulativeIndentation
    return .set [{
      lastLineLength := lineIndentation
      cost := Cost.newlineCost lineIndentation
      -- Reset the level of non-cumulative indentation so that the next non-cumulative `indented`
      -- can increase the level of indentation again.
      hasPendingNonCumulativeIndentation := false
      output :=
        modify fun out => {
          out with
          rendering := out.rendering ++ "\n" |>.pushn ' ' lineIndentation
        }
    }]
  | .text s =>
    return .set [{
      lastLineLength := columnPos + s.chars.length
      cost := Cost.textCost columnPos s.chars.length
      hasPendingNonCumulativeIndentation := nonCumulativeIndentation > 0
      output := modify fun out => { out with rendering := out.rendering ++ s }
    }]
  | .tagged id d =>
    let ms ← MeasureSet.resolve d columnPos indentation nonCumulativeIndentation fullness
    return ms.addTag id
  | .unflattenable _ | .flattened _ =>
    -- Eliminated during pre-processing.
    panic! "Encountered `flattened` that should have been eliminated during pre-processing"
  | .indented n isCumulative d =>
    if isCumulative then
      let ms ← MeasureSet.resolve d columnPos (indentation + n) nonCumulativeIndentation fullness
      return ms
    else
      -- Sets the level of non-cumulative indentation to `n`.
      -- In a chain of nested non-cumulative `indent`s, the innermost `n` is used.
      let ms ← MeasureSet.resolve d columnPos indentation n fullness
      return ms.setHasPendingNonCumulativeIndentation nonCumulativeIndentation
  | .aligned d =>
    -- Sets the level of indentation to `columnPos` and resets the level of
    -- non-cumulative indentation, as the alignment dictates the level of indentation in `d`.
    let ms ← MeasureSet.resolve d columnPos columnPos 0 fullness
    return ms.setHasPendingNonCumulativeIndentation nonCumulativeIndentation
  | .unindented onlyNonCumulative d =>
    let indentation :=
      if onlyNonCumulative then
        indentation
      else
        0
    let ms ← MeasureSet.resolve d columnPos indentation 0 fullness
    return ms.setHasPendingNonCumulativeIndentation nonCumulativeIndentation
  | .final d =>
    -- The failure condition of `final` ensures that `fullness.isFullAfter` is true when we reach
    -- this point. However, within `final`, the `final` node imposes no constraints, so we
    -- case-split on `fullness.isFullAfter` here.
    let set1 ←
      MeasureSet.resolve d columnPos indentation nonCumulativeIndentation
        (fullness.setFullAfter false)
    let set2 ←
      MeasureSet.resolve d columnPos indentation nonCumulativeIndentation
        (fullness.setFullAfter true)
    return .merge set1 set2 (prunable := false)
  | .initial d =>
    -- Dual to `final`: the failure condition of `initial` ensures that `fullness.isInitialBefore`
    -- is true when we reach this point, but within `initial`, the `initial` node imposes no
    -- constraints, so we case-split on `fullness.isInitialBefore` here.
    let set1 ←
      MeasureSet.resolve d columnPos indentation nonCumulativeIndentation
        (fullness.setInitialBefore false)
    let set2 ←
      MeasureSet.resolve d columnPos indentation nonCumulativeIndentation
        (fullness.setInitialBefore true)
    return .merge set1 set2 (prunable := false)
  | .free d =>
    let set ← MeasureSet.resolve d columnPos indentation nonCumulativeIndentation fullness
    let .ok measure ← set.extractAtMostOne? (taintedResolution := true)
      | return .set []
    return .set [measure.makeFreeAt columnPos]
  | .guarded p d =>
    if ! p.assertion columnPos indentation nonCumulativeIndentation then
      return .set []
    return ← MeasureSet.resolve d columnPos indentation nonCumulativeIndentation fullness
  | .costing c d =>
    let ms ← MeasureSet.resolve d columnPos indentation nonCumulativeIndentation fullness
    return ms.addCost c
  | .either d1 d2 =>
    let set1 ← MeasureSet.resolve d1 columnPos indentation nonCumulativeIndentation fullness
    let set2 ← MeasureSet.resolve d2 columnPos indentation nonCumulativeIndentation fullness
    return .merge set1 set2 (prunable := false)
  | .append d1 d2 =>
    -- We can't tell whether the position between `d1` and `d2` will be full or initial in
    -- advance, which decides whether we need to set `isFullAfter` and `isInitialAfter` on the
    -- left side of the `append` and `isFullBefore` and `isInitialBefore` on the right side of
    -- the `append`, so we case-split on these four alternatives and then later prune subtrees
    -- that are inconsistent with the given fullness state.
    let analyze (isMidFull isMidInitial : Bool) : ResolverM σ τ (MeasureSet τ) :=
      analyzeAppend d d1 d2 columnPos indentation nonCumulativeIndentation fullness isMidFull
        isMidInitial
    let set1 ← analyze false false
    let set2 ← analyze false true
    let set3 ← analyze true false
    let set4 ← analyze true true
    return .merge (.merge set1 set2 (prunable := false)) (.merge set3 set4 (prunable := false))
      (prunable := false)
where
  /--
  Resolves `d1` to a measure set, then resolves `d2` with each of the column positions in the
  measure set of `d1` and finally appends each measure from resolving `d2` to each measure from
  resolving `d1`.
  At the end, the invariants for sets of measures (documented at `MeasureSet.Set`) are enforced.
  -/
  analyzeAppend
      (d d1 d2 : Doc τ) (columnPos indentation nonCumulativeIndentation : Nat)
      (fullness : FullnessState) (isMidFull isMidInitial : Bool)
      : ResolverM σ τ (MeasureSet τ) := do
    let fullness1 := fullness.setFullAfter isMidFull |>.setInitialAfter isMidInitial
    let fullness2 := fullness.setFullBefore isMidFull |>.setInitialBefore isMidInitial
    -- `d2` is resolved in `fullness2` for every measure of `d1`, so if it is already known to fail
    -- there, resolving `d1` cannot contribute any measure. Checking this up-front prunes the
    -- inconsistent alternatives of the case split above before paying for the left side, which
    -- matters most when `d2` is a text node adjacent to the boundary.
    if d2.isFailure fullness2 then
      return .set []
    let set1 ← MeasureSet.resolve d1 columnPos indentation nonCumulativeIndentation fullness1
    match set1 with
    | .tainted tm1 =>
      return .tainted (.taintedAppend tm1 d2 indentation nonCumulativeIndentation fullness2
        d.maxNewlineCount?)
    | .set ms1 =>
      ms1.foldrM (init := MeasureSet.set []) fun m1 acc => do
        let (indentation2, nonCumulativeIndentation2) :=
          if m1.hasPendingNonCumulativeIndentation then
            (indentation, nonCumulativeIndentation)
          else
            (indentation + nonCumulativeIndentation, 0)
        let set2 ←
          MeasureSet.resolve d2 m1.lastLineLength indentation2 nonCumulativeIndentation2 fullness2
        let m1Result : MeasureSet τ :=
          match set2 with
          | .tainted tm2 =>
            .tainted (.appendTainted m1 tm2 d.maxNewlineCount?)
          | .set [] =>
            .set []
          | .set ms2 =>
            .set <|
              -- `ms2` fulfills the measure set invariants. Since `Measure.append` shifts costs
              -- uniformly by `m1.cost` and leaves `lastLineLength` and
              -- `hasPendingNonCumulativeIndentation` untouched, the appended list is still sorted
              -- by `lastLineLength` desc with T preceding F at ties. New dominations can arise
              -- when `+` is not strictly monotone (e.g. `a + b := max(a, b)`): distinct costs may
              -- collapse to equal cost, both within a same-pending sublist (where a later,
              -- smaller-`lastLineLength` measure then dominates an earlier one) and across
              -- pending (where a T-pending measure newly dominates an F-pending measure at
              -- smaller-or-equal `lastLineLength`). `Set.dedup` cleans both up in linear time.
              MeasureSet.Set.dedup (ms2.map m1.append)
        -- `m1Result` and (inductively) all results in `acc` are resolutions of `d2` in `fullness2`,
        -- so unless `d2` has context-dependent failure, all resolutions being merged here either
        -- fail at once or none of them fail.
        return m1Result.merge acc (prunable := ! d2.hasContextDependentFailure fullness2)

/--
Determines the set of measures for a given resolution context and memoizes all nodes along the way.
-/
partial def MeasureSet.resolve : Resolver σ τ :=
  Resolver.memoize fun d columnPos indentation nonCumulativeIndentation fullness => do
    -- Lifting both the memoization of the root node and the taintedness check out to
    -- `MeasureSet.resolve` ensures that we can use `resolveCore` to resolve `resolveTainted` nodes
    -- in the resolver for tainted measures.
    let columnPos' :=
      if let .text s := d then
        columnPos + s.chars.length
      else
        columnPos
    if columnPos' > Cost.optimalityCutoffWidth τ
      || indentation + nonCumulativeIndentation > Cost.optimalityCutoffWidth τ
    then
      return .tainted (.resolveTainted d columnPos indentation nonCumulativeIndentation fullness
        d.maxNewlineCount?)
    return ← MeasureSet.resolveCore d columnPos indentation nonCumulativeIndentation fullness

/--
Checks whether we have a memoized result for a given tainted measure and if so, uses that.
Otherwise, `f` is evaluated and the result is memoized.

We memoize all tainted resolution results because tainted measures can be shared during resolution,
and resolving a shared tainted measure again would repeat work.
-/
@[specialize]
partial def TaintedResolver.memoize (f : TaintedResolver σ τ) : TaintedResolver σ τ := fun tm => do
  let cachedResolvedTainted? ← getCachedResolvedTainted? tm
  if let .hit m := cachedResolvedTainted? then
    return m
  let m? ← f tm
  setCachedResolvedTainted tm m?
  return m?

partial def TaintedMeasure.resolve? : TaintedResolver σ τ :=
  TaintedResolver.memoize fun tm => do
    match tm with
    | .mergeTainted tm1 tm2 _ =>
      -- The first alternative can only fail if it contains a document with context-dependent
      -- failure.
      let some m1 ← tm1.resolve?
        | let m2? ← tm2.resolve?
          return m2?
      return some m1
    | .taintedAppend tm d indentation nonCumulativeIndentation fullness _ =>
      -- If `d` has context-dependent failure, it can fail after the measure chosen for `tm` but
      -- succeed after another one. Other measures are not tried, so such renderings can be lost.
      let some m1 ← tm.resolve?
        | return none
      let (indentation2, nonCumulativeIndentation2) :=
        if m1.hasPendingNonCumulativeIndentation then
          (indentation, nonCumulativeIndentation)
        else
          (indentation + nonCumulativeIndentation, 0)
      let ms2 ←
        MeasureSet.resolve d m1.lastLineLength indentation2 nonCumulativeIndentation2 fullness
      let .ok m2 ← ms2.extractAtMostOne? (taintedResolution := true)
        | return none
      return some <| m1.append m2
    | .appendTainted m1 tm2 _ =>
      let some m2 ← tm2.resolve?
        | return none
      return some <| m1.append m2
    | .setTaintedHasPendingNonCumulativeIndentation tm pendingNonCumulativeIndentation _ =>
      let some m ← tm.resolve?
        | return none
      return some <| m.setHasPendingNonCumulativeIndentation pendingNonCumulativeIndentation
    | .addTag tm tag _ =>
      let some m ← tm.resolve?
        | return none
      return some <| m.addTag tag
    | .addCost tm c _ =>
      let some m ← tm.resolve?
        | return none
      return some <| m.addCost c
    | .resolveTainted d columnPos indentation nonCumulativeIndentation fullness _ =>
      -- If we used `resolve` instead of `resolveCore` here, we would just again obtain a tainted
      -- measure, and the mutual recursion between `MeasureSet.extractAtMostOne?` and
      -- `TaintedMeasure.resolve?` would make no progress.
      -- Using `resolveCore`, which does not perform taintedness checks and does not memoize the
      -- result of resolving the root node, ensures that we make progress on the root node.
      -- This resolution may again produce tainted measures for the children of `d`, which will then
      -- be resolved recursively.
      let ms ← MeasureSet.resolveCore d columnPos indentation nonCumulativeIndentation fullness
      return (← ms.extractAtMostOne? (taintedResolution := true)).toOption

/--
Yields the measure in a non-tainted measure set with the lowest cost and amongst measures with the
lowest cost, the one with the smallest last line length.
For a tainted measure, resolves the tainted measure to a regular measure.
-/
partial def MeasureSet.extractAtMostOne? (ms : MeasureSet τ) (taintedResolution : Bool)
    : ResolverM σ τ (Except FormattingError (Measure τ)) := do
  match ms with
  | .tainted tm =>
    if !taintedResolution then
      return .error .tainted
    let some m ← tm.resolve?
      | return .error .failure
    return .ok m
  | .set ms =>
    -- The set is sorted by `lastLineLength` desc with cost strictly ascending only *within*
    -- each `hasPendingNonCumulativeIndentation` sublist; across pending values there is no
    -- cost constraint (e.g. `[(10, 5, T), (5, 3, F)]` is a valid set), so the head is no
    -- longer guaranteed to have the lowest cost. A linear scan finds the lowest-cost measure,
    -- breaking cost ties by smallest `lastLineLength`.
    let some m :=
        ms.foldl (init := none) fun
          | none, m =>
            some m
          | some best, m =>
            if !(best.cost ≤ m.cost) then
              some m
            else if !(m.cost ≤ best.cost) then
              some best
            else if m.lastLineLength < best.lastLineLength then
              some m
            else
              some best
      | return .error .failure
    return .ok m

end

/--
Resolves a document to a measure with the given initial offset, or `none` if the resolution
failed, i.e. if there is no interpretation of `d` that does not result in `failure`.
-/
def resolve? (d : Doc τ) (offset : Nat) (taintedResolution : Bool)
    : Except FormattingError (Measure τ) :=
  runST fun _ =>
    ResolverM.run do
      -- We cannot tell in advance whether the last line of `d` will be full or whether its first line
      -- will be initial, so we case split on `isFullAfter` and `isInitialBefore` of the fullness
      -- state and later prune subtrees of the search when we notice that they are inconsistent with
      -- the actual document. In particular, this means that the start and the end of the document are
      -- treated as the start and the end of a line, independently of `offset`.
      let resolveAt (isFullAfter isInitialBefore : Bool) :=
        MeasureSet.resolve d offset 0 0
          (.mk (isFullBefore := false) isFullAfter isInitialBefore (isInitialAfter := false))
      let ms1 ← resolveAt false false
      let ms2 ← resolveAt false true
      let ms3 ← resolveAt true false
      let ms4 ← resolveAt true true
      let ms :=
        (ms1.merge ms2 (prunable := false)).merge (ms3.merge ms4 (prunable := false))
          (prunable := false)
      ms.extractAtMostOne? taintedResolution

/--
Formats a document to a string for a given cost function.
Yields `none` if the resolution failed, i.e. if there is no interpretation of `d` that does not
result in `failure`.
-/
public def formatWithCost?
    {τ : Type} [BEq τ] [Hashable τ] [Zero τ] [Add τ] [LE τ] [DecidableLE τ] [Cost τ]
    (d : Doc τ) (taintedResolution : Bool)
    (offset : Nat := 0)
    : Except FormattingError Output := do
  let d := d.preprocess
  let m ← resolve? d offset taintedResolution
  return m.print

/--
Default cost function for the formatter.

Minimizes the sum of squared overflows over a page width limit `softWidth`. This means that the
formatter will find renderings with smaller overflows even when all possible renderings for a
document overflow the page width limit.
Amongst renderings with the same sum of squared overflows (or no overflows), it minimizes the
amount of newlines in the document.

If the width of all renderings of a document exceed a parameter `optimalityCutoffWidth`,
the formatter will not attempt to determine an optimal rendering with the least amount of overflow
amongst these renderings. Instead, it heuristically chooses a rendering using an approximation for
the amount of newlines, and picks the rendering with the largest approximation for the amount of
newlines.

`optimalityCutoffWidth` bounds the worst-case time complexity of the formatter.
It does not represent the actual page limit and should always be chosen to be larger than
`softWidth`.
-/
public structure DefaultCost (softWidth : Nat) (optimalityCutoffWidth : Nat) where
  failureFallbackPenalty : Nat
  overflowCost : Nat
  overflowFallbackPenalty : Nat
  heightCost : Nat
  heightFallbackPenalty : Nat
deriving BEq, Hashable

def DefaultCost.ofCosts (overflowCost heightCost : Nat) : DefaultCost w W where
  failureFallbackPenalty := 0
  overflowCost
  overflowFallbackPenalty := 0
  heightCost
  heightFallbackPenalty := 0

public def DefaultCost.ofFailureFallbackPenalty (c : Nat) : DefaultCost w W where
  failureFallbackPenalty := c
  overflowCost := 0
  overflowFallbackPenalty := 0
  heightCost := 0
  heightFallbackPenalty := 0

public def DefaultCost.ofOverflowFallbackPenalty (c : Nat) : DefaultCost w W where
  failureFallbackPenalty := 0
  overflowCost := 0
  overflowFallbackPenalty := c
  heightCost := 0
  heightFallbackPenalty := 0

public def DefaultCost.ofHeightFallbackPenalty (c : Nat) : DefaultCost w W where
  failureFallbackPenalty := 0
  overflowCost := 0
  overflowFallbackPenalty := 0
  heightCost := 0
  heightFallbackPenalty := c

def DefaultCost.zero : DefaultCost w W := .ofCosts 0 0

def DefaultCost.add (c1 c2 : DefaultCost w W) : DefaultCost w W := ⟨
  c1.failureFallbackPenalty + c2.failureFallbackPenalty,
  c1.overflowCost + c2.overflowCost,
  c1.overflowFallbackPenalty + c2.overflowFallbackPenalty,
  c1.heightCost + c2.heightCost,
  c1.heightFallbackPenalty + c2.heightFallbackPenalty
⟩

@[no_expose]
public instance : Zero (DefaultCost w W) where
  zero := DefaultCost.zero

@[no_expose]
public instance : Add (DefaultCost w W) where
  add := DefaultCost.add

def DefaultCost.le (c1 c2 : DefaultCost w W) : Bool :=
  if c1.failureFallbackPenalty ≠ c2.failureFallbackPenalty then
    c1.failureFallbackPenalty < c2.failureFallbackPenalty
  else if c1.overflowCost ≠ c2.overflowCost then
    c1.overflowCost < c2.overflowCost
  else if c1.overflowFallbackPenalty ≠ c2.overflowFallbackPenalty then
    c1.overflowFallbackPenalty < c2.overflowFallbackPenalty
  else if c1.heightCost ≠ c2.heightCost then
    c1.heightCost < c2.heightCost
  else
    c1.heightFallbackPenalty ≤ c2.heightFallbackPenalty

@[no_expose]
public instance : LE (DefaultCost w W) where
  le c1 c2 := DefaultCost.le c1 c2

@[no_expose]
public instance : DecidableLE (DefaultCost w W) := fun _ _ => inferInstanceAs (Decidable (_ = true))

def DefaultCost.textCost (softWidth optimalityCutoffWidth columnPos length : Nat)
    : DefaultCost softWidth optimalityCutoffWidth :=
  if columnPos + length <= softWidth then
    -- `softWidth` not exceeded => no cost
    .ofCosts 0 0
  else if columnPos <= softWidth then
    -- `softWidth` first exceeded with this text node by `columnPos + length - softWidth`
    -- => cost of `(columnPos + length - softWidth)^2`
    let lengthOverflow := (columnPos + length) - softWidth
    .ofCosts (lengthOverflow * lengthOverflow) 0
  else
    -- This text node is being placed at a column position that already exceeds `softWidth`,
    -- which means that we have already booked costs for another text node before this one on
    -- the same line.
    -- We want the sum of these two costs to represent the combined squared overflow over
    -- `softWidth` so that the sum of all costs of the text nodes on a line denotes the total
    -- squared overflow.
    --
    -- Assume that the cost `c₁` of the text nodes that have already been placed on this line prior
    -- to this one represents the squared overflow over `softWidth` so far, i.e. that
    -- `c₁ = (columnPos - softWidth)^2` (the induction basis for this assumption is given by the
    -- first two branches of this function).
    --
    -- We now want to choose a cost `c₂` for this text node with
    -- `c₁ + c₂ = (columnPos + length - softWidth)^2` to maintain the invariant.
    -- With `columnPos > softWidth` and `(a + b)^2 - a^2 = b*(2*a + b)`, we have
    -- ```
    -- c₁ + c₂ = (columnPos - softWidth)^2 + c₂ = (columnPos + length - softWidth)^2 iff
    -- c₂ = (columnPos - softWidth + length)^2 - (columnPos - softWidth)^2
    --    = length*(2*(columnPos - softWidth) + length)
    -- ```.
    let columnPosOverflow := columnPos - softWidth
    let lengthOverflow := length
    .ofCosts (lengthOverflow * (2 * columnPosOverflow + lengthOverflow)) 0

def DefaultCost.newlineCost (w W _length : Nat) : DefaultCost w W := .ofCosts 0 1

@[no_expose]
public instance : Cost (DefaultCost softWidth optimalityCutoffWidth) where
  textCost := DefaultCost.textCost softWidth optimalityCutoffWidth
  newlineCost := DefaultCost.newlineCost softWidth optimalityCutoffWidth
  optimalityCutoffWidth := optimalityCutoffWidth

/--
Formats a document to a string with the default cost function for a given page width limit `width`.
Yields `none` if the resolution failed, i.e. if there is no interpretation of `d` that does not
result in `failure`.

The default cost function minimizes the sum of squared overflows over `width`. This means that the
formatter will find renderings with smaller overflows even when all possible renderings for a
document overflow the page width limit.
Amongst renderings with the same sum of squared overflows (or no overflows), it minimizes the
amount of newlines in the document.

If the width of all renderings of a document exceed `optimalityCutoffWidth`,
the formatter will not attempt to determine an optimal rendering with the least amount of overflow
amongst these renderings. Instead, it heuristically chooses a rendering using an approximation for
the amount of newlines, and picks the rendering with the largest approximation for the amount of
newlines.

`optimalityCutoffWidth` bounds the worst-case time complexity of the formatter.
It does not represent the actual page limit and should always be chosen to be larger than
`width`.
-/
public def format?
    (width : Nat) (optimalityCutoffWidth : Nat) (d : Doc (DefaultCost width optimalityCutoffWidth))
    (taintedResolution : Bool)
    (offset : Nat := 0)
    : Except FormattingError Output := do
  formatWithCost? d taintedResolution offset
