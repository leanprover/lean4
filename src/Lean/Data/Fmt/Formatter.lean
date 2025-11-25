/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Basic
public import Std.Data.HashSet.Basic

/-!
`Fmt` formatter.

This file implements the formatter of 'A Pretty Expressive Printer' [1] by
Sorawee Porncharoenwase, Justin Pombrio and Emina Torlak.
This implementation is based on the Racket implementation of pretty-expressive [2].

[1] https://arxiv.org/pdf/2310.01530
[2] https://docs.racket-lang.org/pretty-expressive/
-/

namespace Lean.Fmt

open Std

/--
Whether the formatter should memoize the given document.
Since memoization in itself can be expensive, not all documents are memoized, only every n-th layer.
Time-complexity-wise, this is sound because the formatting document is a binary tree, and so its
height bounds the amount of nodes in the tree.
-/
def Doc.shouldMemoize (d : Doc) : Bool :=
  d.memoHeight = 0

structure PreprocessingCacheKey where
  docPtr : USize
  isFlattened : Bool
  deriving BEq, Hashable

structure PreprocessingState where
  cache : HashMap PreprocessingCacheKey Doc := {}

/--
Erases all `flattened` nodes from a document by flattening all newlines with each `flattened` node.

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
def Doc.preprocess (d : Doc) : Doc :=
  goMemoized d false |>.run' {}
where
  goMemoized (d : Doc) (isFlattened : Bool) : StateM PreprocessingState Doc := do
    let cacheKey := { docPtr := unsafe ptrAddrUnsafe d, isFlattened }
    -- Re-using cached preprocessing results is essential for not destroying the
    -- shared structure of the input document.
    if let some d' := (← get).cache.get? cacheKey then
      return d'
    let d' ← go d isFlattened
    modify fun s => { s with cache := s.cache.insert cacheKey d' }
    return d'
  go (d : Doc) (isFlattened : Bool) : StateM PreprocessingState Doc := do
    match d with
    | .newline f? =>
      if isFlattened then
        let some f := f?
          | return .failure
        return .text f
      else
        return .newline none
    | .flattened d =>
      goMemoized d true
    | .failure
    | .text .. =>
      return d
    | .indented n d =>
      let d ← goMemoized d isFlattened
      return .indented n d
    | .aligned d =>
      let d ← goMemoized d isFlattened
      return .aligned d
    | .unindented d =>
      let d ← goMemoized d isFlattened
      return .unindented d
    | .full d =>
      let d ← goMemoized d isFlattened
      return .full d
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

/--
A measure is a tuple of the compound cost of a specific rendering and a writer monad to produce the
rendering.

The compound cost of a measure consists of both a configurable cost (as defined by a configurable
cost function) and the current length of the last line of the rendering.
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
  Configurable cost (as definited by the cost function) of the rendering represented by this
  measure.
  -/
  cost : τ
  /--
  Writer monad that produces the rendering that this measure presents.
  -/
  output : StateM String Unit

variable {τ : Type} [Add τ] [LE τ] [DecidableLE τ] [Cost τ]

/--
Whether a measure subsumes another measure. See the documentation of `Measure` for details on
what measure domination entails.
-/
def Measure.dominates (m1 m2 : Measure τ) : Bool :=
  m1.lastLineLength <= m2.lastLineLength && m1.cost <= m2.cost

/-- Determines the measure that represents the concatenation of the renderings of two measures. -/
def Measure.append (m1 m2 : Measure τ) : Measure τ where
  lastLineLength := m2.lastLineLength
  cost := m1.cost + m2.cost
  output := do
    m1.output
    m2.output

/-- Runs the writer monad of a measure, printing its rendering to a string. -/
def Measure.print (m : Measure τ) : String :=
  let (_, printed) := m.output.run ""
  printed

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

  Since there are only four different fullness states in which each document can be resolved and
  potentially fail, since the failure of resolution is independent of column position and
  indentation, and since the resolver for tainted measures memoizes whether a resolution failed,
  the resolver for tainted measures will only need to try resolving at most `4*amount of documents`
  alternatives overall, so the time complexity of the formatter remains bounded.
  -/
  | mergeTainted (tm1 tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  /--
  Append a document to the rendering of a tainted measure. Resolving this tainted measure amounts to
  resolving the tainted measure on the left, resolving the document on the right in the column
  position after resolving the tainted measure on the left and with the given indentation and
  fullness state, picking a measure from the set of measures of the resolution on the right
  and then appending those.
  -/
  | taintedAppend (tm1 : TaintedMeasure τ) (d2 : Doc) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)
  /--
  Append a tainted measure to a regular measure. Resolving this tainted measure amounts to simply
  resolving the tainted measure on the right and appending it to the measure on the left.
  -/
  | appendTainted (m1 : Measure τ) (tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  /--
  Resolve a tainted measure for a given resolution context to a regular measure.
  Amounts to resolving the given document in the given context, picking a measure from the set of
  measures produced by the resolution and memoizing whether the resolution failed so that
  no failed resolution of a tainted measure is tried twice in the same fullness state and the time
  complexity for tainted measure resolution remains bounded by `4*amount of documents`.

  Notably, the resolution of the document in the given context skips the taintedness-check for the
  top level node, so this will process the top-level node of the document and then recurse with
  potentially tainted child documents until eventually the full tainted measure is resolved.
  -/
  | resolveTainted (d : Doc) (columnPos : Nat) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)

/-- Approximation for the maximum amount of newlines in the rendering of a tainted measure. -/
def TaintedMeasure.maxNewlineCount? : TaintedMeasure τ → Option Nat
  | .mergeTainted (maxNewlineCount? := n) .. => n
  | .taintedAppend (maxNewlineCount? := n) .. => n
  | .appendTainted (maxNewlineCount? := n) .. => n
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
2. The set of non-tainted measures is sorted by last line length (strictly descending).

Together, these two invariants also imply that the set of non-tainted measures is sorted
by cost (strictly ascending), as otherwise the first invariant would be violated.

Since all of these measures are non-tainted, both invariants individually imply that there are
at most W measures in a given set of non-tainted measures, where W is the optimality cutoff width
of the cost function.
-/
abbrev MeasureSet.Set (τ : Type) := List (Measure τ)

/-- Merges two sets of non-tainted measures, maintaining their invariants in the result. -/
partial def MeasureSet.Set.merge (ms1 ms2 : MeasureSet.Set τ) : MeasureSet.Set τ :=
  match ms1, ms2 with
  | [], _ => ms2
  | _, [] => ms1
  | m1 :: ms1', m2 :: ms2' =>
    if m1.dominates m2 then
      merge ms1 ms2'
    else if m2.dominates m1 then
      merge ms1' ms2
    else if m1.lastLineLength > m2.lastLineLength then
      m1 :: merge ms1' ms2
    else
      m2 :: merge ms1 ms2'

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
Memoization key for sets of measures produced by the formatter.
Includes the full context that uniquely determines a set of measures:
- A pointer to the document that is being formatted
- The column position at which the document is being formatted
- The current level of indentation within which the document is being formatted
- The fullness state surrounding the document
-/
structure SetCacheKey where
  docPtr : USize
  columnPos : Nat
  indentation : Nat
  fullness : FullnessState
  deriving BEq, Hashable

/--
Memoization key for tracking whether a document has failed in the resolver for tainted measures.
Since resolution failure only depends on the document and the fullness state surrounding it,
this key does not contain the column position or the current indentation level.

Memoizing the failure state in the resolver for tainted measures ensures that we never have to
resolve a single document (as identified by its pointer) more than 4 times.
-/
structure FailureCacheKey where
  docPtr : USize
  fullness : FullnessState
  deriving BEq, Hashable

/--
State of the resolver and the resolver for tainted measures, which runs after the regular resolver.

Maintains three separate memoization caches:
- `setCache`, which memoizes sets of measures that are produced during resolution per `SetCacheKey`.
  This is the main memoization cache of the formatter. It memoizes all resolution results for all
  documents with `shouldMemoize = true` and ensures that the time complexity of resolution remains
  reasonable.
  After resolution, the `setCache` is re-used in resolutions performed by the resolution of tainted
  measures. Notably, in the resolution of tainted measures, it is not used for resolving the
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
- `failureCache`, which memoizes whether resolving a document in a given fullness state resulted
  in a failure. Resolution failure depends only on the document and the given fullness state that
  the document is resolved in, so this cache allows pruning subtrees of the search more
  aggressively.
  In the resolver for tainted measures, this cache also ensures that we never try to resolve the
  same document more than four times, which bounds the time complexity of the tainted resolver.
  In the Racket implementation, this cache is a mutable cache on the document that is only used
  in the resolver for tainted measures to bound its time complexity. However, we've found that
  performance improves when also enabling it for the regular resolver.
-/
structure ResolutionState (τ : Type) where
  setCache : HashMap SetCacheKey (MeasureSet τ) := {}
  resolvedTaintedCache : HashMap USize (Option (Measure τ)) := {}
  failureCache : HashSet FailureCacheKey := {}

/--
Monad for resolving a document in a resolution context to a set of measures.
Uses `StateRefT` to avoid having to box the state together with return values during resolution.
-/
abbrev ResolverM (σ τ : Type) := StateRefT (ResolutionState τ) (ST σ)

def ResolverM.run (f : ResolverM σ τ α) : ST σ α :=
  f.run' {}

@[inline]
def getCachedSet? (d : Doc) (columnPos indentation : Nat) (fullness : FullnessState) :
    ResolverM σ τ (Option (MeasureSet τ)) := do
  return (← get).setCache.get? {
    docPtr := unsafe ptrAddrUnsafe d
    columnPos
    indentation
    fullness
  }

@[inline]
def setCachedSet (d : Doc) (columnPos indentation : Nat) (fullness : FullnessState)
    (set : MeasureSet τ) : ResolverM σ τ Unit :=
  modify fun state => { state with
    setCache := state.setCache.insert {
        docPtr := unsafe ptrAddrUnsafe d
        columnPos
        indentation
        fullness
      } set
  }

inductive CacheResult (α : Type) where
  | miss
  | hit (cached : α)

@[inline]
def getCachedResolvedTainted? (tm : TaintedMeasure τ) :
    ResolverM σ τ (CacheResult (Option (Measure τ))) := do
  match (← get).resolvedTaintedCache.get? (unsafe ptrAddrUnsafe tm) with
  | none => return .miss
  | some cached? => return .hit cached?

@[inline]
def setCachedResolvedTainted (tm : TaintedMeasure τ) (m? : Option (Measure τ)) :
    ResolverM σ τ Unit :=
  modify fun state => { state with
    resolvedTaintedCache := state.resolvedTaintedCache.insert (unsafe ptrAddrUnsafe tm) m?
  }

def Doc.isLeaf : Doc → Bool
  | .failure => true
  | .newline .. => true
  | .text .. => true
  | _ => false

def isFailing (d : Doc) (fullness : FullnessState) : ResolverM σ τ Bool := do
  if d.isLeaf then
    -- For leaf nodes, guaranteed failure is fully determinined by `Doc.isFailure`.
    return d.isFailure fullness
  else if d.isFailure fullness then
    -- For some inner nodes (`full` specifically), we can prune specific subtrees
    -- if `Doc.isFailure` yields `true` and have no information about failure otherwise.
    return true
  else
    -- For all other nodes, if we have already determined that a document fails in a given fullness
    -- state, we can prune that subtree.
    let isCachedFailure := (← get).failureCache.contains {
      docPtr := unsafe ptrAddrUnsafe d
      fullness
    }
    return isCachedFailure

def setCachedFailing (d : Doc) (fullness : FullnessState) : ResolverM σ τ Unit :=
  modify fun state => { state with
    failureCache := state.failureCache.insert {
      docPtr := unsafe ptrAddrUnsafe d
      fullness
    }
  }

def Resolver (σ τ : Type) :=
  (d : Doc) → (columnPos indentation : Nat) → (fullness : FullnessState) →
    ResolverM σ τ (MeasureSet τ)

/--
Checks whether we have a memoized result for a given resolution context and uses that.
Otherwise, `f` is evaluated and the result is memoized if `Doc.shouldMemoize` is true.
-/
@[specialize]
def Resolver.memoize (f : Resolver σ τ) : Resolver σ τ := fun d columnPos indentation fullness => do
  if ← isFailing d fullness then
    return .set []
  if columnPos > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ
      || ! d.shouldMemoize then
    let r ← f d columnPos indentation fullness
    if r matches .set [] then
      setCachedFailing d fullness
    return r
  if let some cachedSet ← getCachedSet? d columnPos indentation fullness then
    return cachedSet
  let r ← f d columnPos indentation fullness
  setCachedSet d columnPos indentation fullness r
  if r matches .set [] then
    setCachedFailing d fullness
  return r

mutual

/--
Determines the set of measures for a given resolution context.
The root node is not memoized, while nodes below the root node can be memoized.
-/
partial def MeasureSet.resolveCore : Resolver σ τ := fun d columnPos indentation fullness => do
  match d with
  | .failure =>
    return .set []
  | .newline .. =>
    return .set [{
      lastLineLength := indentation
      cost := Cost.newlineCost indentation
      output := modify fun out =>
         out ++ "\n" |>.pushn ' ' indentation
    }]
  | .text s =>
    return .set [{
      lastLineLength := columnPos + s.length
      cost := Cost.textCost columnPos s.length
      output := modify fun out =>
        out ++ s
    }]
  | .flattened _ =>
    -- Eliminated during pre-processing.
    unreachable!
  | .indented n d =>
    resolve d columnPos (indentation + n) fullness
  | .aligned d =>
    resolve d columnPos columnPos fullness
  | .unindented d =>
    resolve d columnPos 0 fullness
  | .full d =>
    -- The failure condition of `full` ensures that `fullness.isFullAfter` is true when we reach
    -- this point. However, within `full`, the `full` node imposes no constraints, so we case-split
    -- on `fullness.isFullAfter` here.
    let set1 ← resolve d columnPos indentation (fullness.setFullAfter false)
    let set2 ← resolve d columnPos indentation (fullness.setFullAfter true)
    return .merge set1 set2 (prunable := false)
  | .either d1 d2 =>
    let set1 ← resolve d1 columnPos indentation fullness
    let set2 ← resolve d2 columnPos indentation fullness
    return .merge set1 set2 (prunable := false)
  | .append d1 d2 =>
    -- We can't tell whether the line at the end of `d1` will be full in advance, which decides
    -- whether we need to set `isFullAfter` on the left side of the `append` and `isFullBefore`
    -- on the right side of the `append`, so we case-split on these two alternatives and then
    -- later prune subtrees that are inconsistent with the given fullness state.
    let set1 ← analyzeAppend d d1 d2 columnPos indentation fullness false
    let set2 ← analyzeAppend d d1 d2 columnPos indentation fullness true
    return .merge set1 set2 (prunable := false)
where
  /--
  Resolves `d1` to a measure set, then resolves `d2` with each of the column positions in the
  measure set of `d1` and finally appends each measure from resolving `d2` to each measure from
  resolving `d1`.
  At the end, the invariants for sets of measures (documented at `MeasureSet.Set`) are enforced.
  -/
  analyzeAppend (d d1 d2 : Doc) (columnPos indentation : Nat) (fullness : FullnessState)
      (isMidFull : Bool) : ResolverM σ τ (MeasureSet τ) := do
    let fullness1 := fullness.setFullAfter isMidFull
    let fullness2 := fullness.setFullBefore isMidFull
    let set1 ← resolve d1 columnPos indentation fullness1
    match set1 with
    | .tainted tm1 =>
      return .tainted (.taintedAppend tm1 d2 indentation fullness2 d.maxNewlineCount?)
    | .set ms1 =>
      ms1.foldrM (init := MeasureSet.set []) fun m1 acc => do
        let set2 ← resolve d2 m1.lastLineLength indentation fullness2
        let m1Result : MeasureSet τ :=
          match set2 with
          | .tainted tm2 =>
            .tainted (.appendTainted m1 tm2 d.maxNewlineCount?)
          | .set [] =>
            .set []
          | .set (m2 :: ms2) => .set <| Id.run do
            let mut last := m1.append m2
            let mut deduped := []
            for m2 in ms2 do
              let current := m1.append m2
              -- `ms2` fulfills the measure set invariants, which means that appending these
              -- measures to `m1` results in a set that is still sorted by last line length
              -- in strictly descending order. The resulting set is also still sorted by cost, but
              -- in general not in strictly ascending order, just in ascending order
              -- (by monotonicity of a lawful `+`):
              -- A cost function over ℕ with `a + b := max(a, b)`, ≤ as on the natural numbers and
              -- `textCost` / `newlineCost` defined in some arbitrary lawful manner is lawful,
              -- while `ms2 := [(3, 1), (2, 2), (1, 3)]` fulfills the measure set invariants
              -- and `map ms2 (append (2, 2) ·) = [(3, 2), (2, 2), (1, 3)]` is not strictly
              -- ascending in cost.
              -- The two order invariants imply that we only need to check adjacent measures for
              -- domination and that we only need to check the cost of measures when checking for
              -- domination. The fact that the cost order is not necessarily strict implies that
              -- checking the cost of adjacent measures is still necessary for general lawful cost
              -- functions.
              if current.cost <= last.cost then
                last := current
                continue
              deduped := last :: deduped
              last := current
            return last :: deduped |>.reverse
        -- `m1Result` and (inductively) all results in `acc` are resolutions of `d2`, so all
        -- resolutions being merged here either fail at once or none of them fail.
        -- Hence, we can set `prunable := true` here.
        return m1Result.merge acc (prunable := true)

partial def MeasureSet.resolve : Resolver σ τ := Resolver.memoize fun d columnPos indentation fullness => do
  let columnPos' :=
    if let .text s := d then
      columnPos + s.length
    else
      columnPos
  if columnPos' > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ then
    return .tainted (.resolveTainted d columnPos indentation fullness d.maxNewlineCount?)
  return ← resolveCore d columnPos indentation fullness

end

def TaintedResolver (σ τ : Type) :=
    (tm : TaintedMeasure τ) → ResolverM σ τ (Option (Measure τ))

@[specialize]
def TaintedResolver.memoize (f : TaintedResolver σ τ) : TaintedResolver σ τ := fun tm => do
  let cachedResolvedTainted? ← getCachedResolvedTainted? tm
  if let .hit m := cachedResolvedTainted? then
    return m
  let m? ← f tm
  setCachedResolvedTainted tm m?
  return m?

mutual

partial def TaintedMeasure.resolve? : TaintedResolver σ τ := TaintedResolver.memoize fun tm => do
  match tm with
  | .mergeTainted tm1 tm2 _ =>
    let some m1 ← tm1.resolve?
      | let m2? ← tm2.resolve?
        return m2?
    return some m1
  | .taintedAppend tm d indentation fullness _ =>
    let some m1 ← tm.resolve?
      | return none
    let ms2 ← MeasureSet.resolve d m1.lastLineLength indentation fullness
    let some m2 ← ms2.extractAtMostOne?
      | return none
    return some <| m1.append m2
  | .appendTainted m1 tm2 _ =>
    let some m2 ← tm2.resolve?
      | return none
    return some <| m1.append m2
  | .resolveTainted d columnPos indentation fullness _ =>
    -- TODO: Why resolveCore instead of resolve?
    -- Because it allows us to pop the top-level tainted node and replace it with something else
    let ms ← MeasureSet.resolveCore d columnPos indentation fullness
    let m? ← ms.extractAtMostOne?
    if m?.isNone then
      setCachedFailing d fullness
    return m?

partial def MeasureSet.extractAtMostOne? (ms : MeasureSet τ) : ResolverM σ τ (Option (Measure τ)) := do
  match ms with
  | .tainted tm =>
    tm.resolve?
  | .set ms =>
    return ms.head?

end

def resolve? (d : Doc) (offset : Nat) : Option (Measure τ) := runST fun _ => ResolverM.run do
  let ms1 ← MeasureSet.resolve d offset 0 (.mk false false)
  let ms2 ← MeasureSet.resolve d offset 0 (.mk false true)
  let ms := ms1.merge ms2 (prunable := false)
  ms.extractAtMostOne?

public def formatWithCost? (τ : Type) [Add τ] [LE τ] [DecidableLE τ] [Cost τ]
    (d : Doc) (offset : Nat := 0) : Option String := do
  let d := d.preprocess
  let m ← resolve? (τ := τ) d offset
  return m.print

public structure DefaultCost (softWidth : Nat) (optimalityCutoffWidth : Nat) where
  widthCost : Nat
  heightCost : Nat

def DefaultCost.add (c1 c2 : DefaultCost w W) : DefaultCost w W :=
  ⟨c1.widthCost + c2.widthCost, c1.heightCost + c2.heightCost⟩

@[no_expose]
public instance : Add (DefaultCost w W) where
  add := DefaultCost.add

def DefaultCost.le
    (c1 c2 : DefaultCost w W) : Bool :=
  if c1.widthCost = c2.widthCost then
    c1.heightCost ≤ c2.heightCost
  else
    c1.widthCost ≤ c2.widthCost

@[no_expose]
public instance : LE (DefaultCost w W) where
  le c1 c2 := DefaultCost.le c1 c2

@[no_expose]
public instance : DecidableLE (DefaultCost w W) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

def DefaultCost.textCost (softWidth optimalityCutoffWidth columnPos length : Nat) :
    DefaultCost softWidth optimalityCutoffWidth :=
  if columnPos + length <= softWidth then
    ⟨0, 0⟩
  else if columnPos <= softWidth then
    let lengthOverflow := (columnPos + length) - softWidth
    ⟨lengthOverflow*lengthOverflow, 0⟩
  else
    -- TODO: Explain
    let columnPosOverflow := columnPos - softWidth
    let lengthOverflow := length
    ⟨lengthOverflow*(2*columnPosOverflow + lengthOverflow), 0⟩

def DefaultCost.newlineCost (w W _length : Nat) :
    DefaultCost w W :=
  ⟨0, 1⟩

@[no_expose]
public instance : Cost (DefaultCost softWidth optimalityCutoffWidth) where
  textCost := DefaultCost.textCost softWidth optimalityCutoffWidth
  newlineCost := DefaultCost.newlineCost softWidth optimalityCutoffWidth
  optimalityCutoffWidth := optimalityCutoffWidth

public def format? (d : Doc) (width : Nat)
    (optimalityCutoffWidth : Nat := Nat.max ((5*width)/4) 200)
    (offset : Nat := 0) :
    Option String := do
  formatWithCost? (τ := DefaultCost width optimalityCutoffWidth) d offset

section DefaultCostDefTheorems

public theorem DefaultCost.add_def {c₁ c₂ : DefaultCost w W} :
    c₁ + c₂ = ⟨c₁.widthCost + c₂.widthCost, c₁.heightCost + c₂.heightCost⟩ := by
  simp only [HAdd.hAdd, Add.add, DefaultCost.add]

public theorem DefaultCost.le_def {c₁ c₂ : DefaultCost w W} :
    c₁ ≤ c₂ ↔
      (if c₁.widthCost = c₂.widthCost then
          c₁.heightCost ≤ c₂.heightCost
        else
          c₁.widthCost ≤ c₂.widthCost) := by
  simp only [LE.le]
  simp only [le, Bool.ite_eq_true_distrib, decide_eq_true_eq, Nat.le_eq]

public theorem DefaultCost.textCost_def :
    (Cost.textCost cp n : DefaultCost w W) =
      (if cp + n <= w then
          ⟨0, 0⟩
        else if cp <= w then
          let o := (cp + n) - w
          ⟨o*o, 0⟩
        else
          ⟨n*(2*(cp - w) + n), 0⟩) := by
  simp only [Cost.textCost, textCost]

public theorem DefaultCost.newlineCost_def :
    (Cost.newlineCost n : DefaultCost w W) = ⟨0, 1⟩ := by
  simp only [Cost.newlineCost, newlineCost]

end DefaultCostDefTheorems
