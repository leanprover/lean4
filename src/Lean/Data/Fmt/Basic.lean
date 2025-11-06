/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init.Prelude
public import Init.Data.String.Defs
public import Init.Data.Array
public import Std.Data.HashMap.Basic
public import Init.Data.Hashable
public import Std.Data.HashSet.Basic
public import Std.Data.Iterators

public section

namespace Lean.Fmt

open Std

structure FullnessState where
  isFullBefore : Bool
  isFullAfter : Bool
  deriving BEq, Hashable

abbrev FailureCond := FullnessState → Bool

inductive CoreDoc where
  | failure
  | newline
  | text (s : String)
  | indent (n : Nat) (d : CoreDoc)
  | align (d : CoreDoc)
  | reset (d : CoreDoc)
  | full (d : CoreDoc)
  | either (a b : CoreDoc)
  | concat (a b : CoreDoc)
with
  @[computed_field] isFailure : CoreDoc → FailureCond
    | .failure => fun _ => true
    | .newline => (·.isFullAfter)
    | .text s => fun
      | { isFullBefore := false, isFullAfter := false } => false
      | { isFullBefore := true, isFullAfter := false } => true
      | { isFullBefore := false, isFullAfter := true } => true
      | { isFullBefore := true, isFullAfter := true } => ! s.isEmpty
    | .full _ => (! ·.isFullAfter)
    | _ => fun _ => false
  @[computed_field] maxNewlineCount? : CoreDoc → Option Nat
    | .failure => none
    | .newline => some 1
    | .text _ => some 0
    | .indent _ d
    | .align d
    | .reset d
    | .full d => maxNewlineCount? d
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .concat a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)

def CoreDoc.ptr (doc : CoreDoc) : USize :=
  unsafe ptrAddrUnsafe doc

class Cost (τ : Type) [Add τ] [LE τ] where
  textCost : (columnPos length : Nat) → τ
  newlineCost : (indentationAfterNewline : Nat) → τ
  optimalityCutoffWidth : Nat

  textCost_columnPos_monotone (cp₁ cp₂ n : Nat) :
    cp₁ ≤ cp₂ → textCost cp₁ n ≤ textCost cp₂ n
  textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    textCost cp (n₁ + n₂) = textCost cp n₁ + textCost (cp + n₁) n₂
  newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ → newlineCost i₁ ≤ newlineCost i₂

  add_zero (c : τ) : c + textCost 0 0 = c
  add_comm (c₁ c₂ : τ) : c₁ + c₂ = c₂ + c₁
  add_assoc (c₁ c₂ c₃ : τ) : (c₁ + c₂) + c₃ = c₁ + (c₂ + c₃)

  le_refl (c : τ) : c ≤ c
  le_trans (c₁ c₂ c₃ : τ) : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃
  le_antisymm (c₁ c₂ : τ) : c₁ ≤ c₂ → c₂ ≤ c₁ → c₁ = c₂
  le_total (c₁ c₂ : τ) : c₁ ≤ c₂ ∨ c₂ ≤ c₁

  le_add_invariant (c₁ c₂ c₃ c₄ : τ) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄

variable {τ : Type} [Add τ] [LE τ] [DecidableLE τ] [Cost τ]

structure Measure (τ : Type) where
  lastLineLength : Nat
  cost : τ
  output : StateM String Unit

def Measure.dominates (m1 m2 : Measure τ) : Bool :=
  m1.lastLineLength <= m2.lastLineLength && m1.cost <= m2.cost

def Measure.concat (m1 m2 : Measure τ) : Measure τ where
  lastLineLength := m2.lastLineLength
  cost := m1.cost + m2.cost
  output := do
    m1.output
    m2.output

def Measure.print (m : Measure τ) : String :=
  let (_, printed) := m.output.run ""
  printed

inductive TaintedMeasure (τ : Type) where
  | mergeTainted (tm1 tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  | taintedConcat (tm1 : TaintedMeasure τ) (doc2 : CoreDoc) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)
  | concatTainted (m1 : Measure τ) (tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  | resolveTainted (doc : CoreDoc) (columnPos : Nat) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)

def TaintedMeasure.ptr (tm : TaintedMeasure τ) : USize :=
  unsafe ptrAddrUnsafe tm

def TaintedMeasure.maxNewlineCount? : TaintedMeasure τ → Option Nat
  | .mergeTainted (maxNewlineCount? := n) .. => n
  | .taintedConcat (maxNewlineCount? := n) .. => n
  | .concatTainted (maxNewlineCount? := n) .. => n
  | .resolveTainted (maxNewlineCount? := n) .. => n

def TaintedMeasure.merge (tm1 tm2 : TaintedMeasure τ) (prunable : Bool) : TaintedMeasure τ :=
  let (tm1, tm2) :=
    if Option.le (· <= ·) tm2.maxNewlineCount? tm1.maxNewlineCount? then
      (tm1, tm2)
    else
      (tm2, tm1)
  if prunable then
    tm1
  else
    -- TODO: Is this a good newline approximation?
    .mergeTainted tm1 tm2 tm1.maxNewlineCount?

abbrev MeasureSet.Set (τ : Type) := Array (Measure τ)

def MeasureSet.Set.merge (ms1 ms2 : MeasureSet.Set τ) : MeasureSet.Set τ := Id.run do
  let mut i1 := 0
  let mut i2 := 0
  let mut r := #[]
  while h : i1 < ms1.size ∧ i2 < ms2.size do
    let m1 := ms1[i1]
    let m2 := ms2[i2]
    if m1.dominates m2 then
      i2 := i2 + 1
    else if m2.dominates m1 then
      i1 := i1 + 1
    else if m1.lastLineLength > m2.lastLineLength then
      r := r.push m1
      i1 := i1 + 1
    else
      r := r.push m2
      i2 := i2 + 1
  r := r ++ ms1[i1...*]
  r := r ++ ms2[i2...*]
  return r

def MeasureSet.Set.dedup (ms : MeasureSet.Set τ) : MeasureSet.Set τ := Id.run do
  let mut deduped := #[]
  for previous in ms, current in ms[1:] do
    -- TODO: Why was this sound again?
    if current.cost <= previous.cost then
      continue
    deduped := deduped.push previous
  if let some last := ms[ms.size - 1]? then
    deduped := deduped.push last
  return deduped

inductive MeasureSet (τ : Type) where
  | tainted (tm : TaintedMeasure τ)
  | set (ms : MeasureSet.Set τ)
  deriving Inhabited

def MeasureSet.merge (ms1 ms2 : MeasureSet τ) (prunable : Bool) : MeasureSet τ :=
  match ms1, ms2 with
  | _, .set #[] =>
    ms1
  | .set #[], _ =>
    ms2
  | .tainted tm1, .tainted tm2 =>
    .tainted (tm1.merge tm2 prunable)
  | _, .tainted _ =>
    ms1
  | .tainted _, _ =>
    ms2
  | .set ms1, .set ms2 =>
    .set (ms1.merge ms2)

structure SetCacheKey where
  docPtr : USize
  columnPos : Nat
  indentation : Nat
  fullness : FullnessState
  deriving BEq, Hashable

structure FailureCacheKey where
  docPtr : USize
  fullness : FullnessState
  deriving BEq, Hashable

structure ResolutionState (τ : Type) where
  setCache : HashMap SetCacheKey (MeasureSet τ) := {}
  resolvedTaintedCache : HashMap USize (Option (Measure τ)) := {}
  failureCache : HashSet FailureCacheKey := {}

abbrev ResolverM (τ : Type) := StateM (ResolutionState τ)

def ResolverM.run (f : ResolverM τ α) : α :=
  StateT.run' f {}

def getCachedSet? (doc : CoreDoc) (columnPos indentation : Nat) (fullness : FullnessState) :
    ResolverM τ (Option (MeasureSet τ)) := do
  return (← get).setCache.get? {
    docPtr := doc.ptr
    columnPos
    indentation
    fullness
  }

def setCachedSet (doc : CoreDoc) (columnPos indentation : Nat) (fullness : FullnessState)
    (set : MeasureSet τ) : ResolverM τ Unit :=
  modify fun state => { state with
    setCache := state.setCache.insert {
        docPtr := doc.ptr
        columnPos
        indentation
        fullness
      } set
  }

inductive CacheResult (α : Type)
  | miss
  | hit (cached : α)

def getCachedResolvedTainted? (tm : TaintedMeasure τ) :
    ResolverM τ (CacheResult (Option (Measure τ))) := do
  match (← get).resolvedTaintedCache.get? tm.ptr with
  | none => return .miss
  | some cached? => return .hit cached?

def setCachedResolvedTainted (tm : TaintedMeasure τ) (m? : Option (Measure τ)) :
    ResolverM τ Unit :=
  modify fun state => { state with
    resolvedTaintedCache := state.resolvedTaintedCache.insert tm.ptr m?
  }

def isFailing (doc : CoreDoc) (fullness : FullnessState) : ResolverM τ Bool := do
  let isCachedFailure := (← get).failureCache.contains {
    docPtr := doc.ptr
    fullness
  }
  return isCachedFailure || doc.isFailure fullness

def setCachedFailing (doc : CoreDoc) (fullness : FullnessState) : ResolverM τ Unit :=
  modify fun state => { state with
    failureCache := state.failureCache.insert {
      docPtr := doc.ptr
      fullness
    }
  }

@[expose] def Resolver (τ : Type) :=
  (doc : CoreDoc) → (columnPos indentation : Nat) → (fullness : FullnessState) →
    ResolverM τ (MeasureSet τ)

def Resolver.memoize (f : Resolver τ) : Resolver τ := fun doc columnPos indentation fullness => do
  if ← isFailing doc fullness then
    -- TODO: Set failing, unlike Racket impl?
    return .set #[]
  if columnPos > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ then
    return ← f doc columnPos indentation fullness
  if let some cachedSet ← getCachedSet? doc columnPos indentation fullness then
    return cachedSet
  let r ← f doc columnPos indentation fullness
  setCachedSet doc columnPos indentation fullness r
  return r

mutual

partial def MeasureSet.resolveCore : Resolver τ := fun doc columnPos indentation fullness => do
  match doc with
  | .failure =>
    return .set #[]
  | .newline =>
    return .set #[{
      lastLineLength := indentation
      cost := Cost.newlineCost indentation
      output := modify fun out =>
         out ++ "\n" |>.pushn ' ' indentation
    }]
  | .text s =>
    return .set #[{
      lastLineLength := columnPos + s.length
      cost := Cost.textCost columnPos s.length
      output := modify fun out =>
        out ++ s
    }]
  | .indent n doc =>
    resolve doc columnPos (indentation + n) fullness
  | .align doc =>
    resolve doc columnPos columnPos fullness
  | .reset doc =>
    resolve doc columnPos 0 fullness
  | .full doc =>
    let set1 ← resolve doc columnPos indentation { fullness with isFullAfter := false }
    let set2 ← resolve doc columnPos indentation { fullness with isFullAfter := true }
    return .merge set1 set2 (prunable := false)
  | .either doc1 doc2 =>
    let set1 ← resolve doc1 columnPos indentation fullness
    let set2 ← resolve doc2 columnPos indentation fullness
    return .merge set1 set2 (prunable := false)
  | .concat doc1 doc2 =>
    let set1 ← analyzeConcat doc doc1 doc2 columnPos indentation fullness false
    let set2 ← analyzeConcat doc doc1 doc2 columnPos indentation fullness false
    return .merge set1 set2 (prunable := false)
where
  analyzeConcat (doc doc1 doc2 : CoreDoc) (columnPos indentation : Nat) (fullness : FullnessState)
      (isMidFull : Bool) : ResolverM τ (MeasureSet τ) := do
    let fullness1 := { fullness with isFullAfter := isMidFull }
    let fullness2 := { fullness with isFullBefore := isMidFull }
    let set1 ← resolve doc1 columnPos indentation fullness1
    match set1 with
    | .tainted tm1 =>
      return .tainted (.taintedConcat tm1 doc2 indentation fullness2 doc.maxNewlineCount?)
    | .set ms1 =>
      let mut result := .set #[]
      for m1 in ms1 do
        let set2 ← resolve doc2 m1.lastLineLength indentation fullness2
        match set2 with
        | .tainted tm2 =>
          return .tainted (.concatTainted m1 tm2 doc.maxNewlineCount?)
        | .set ms2 =>
          let m1Result : MeasureSet.Set τ := ms2.map m1.concat
          let m1Result := m1Result.dedup
          result := MeasureSet.merge result (.set m1Result) (prunable := true)
      return result

partial def MeasureSet.resolve : Resolver τ := Resolver.memoize fun doc columnPos indentation fullness => do
  let columnPos' :=
    if let .text s := doc then
      columnPos + s.length
    else
      columnPos
  if columnPos' > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ then
    return .tainted (.resolveTainted doc columnPos indentation fullness doc.maxNewlineCount?)
  return ← resolveCore doc columnPos indentation fullness

end

@[expose] def TaintedResolver (τ : Type) :=
    (tm : TaintedMeasure τ) → ResolverM τ (Option (Measure τ))

def TaintedResolver.memoize (f : TaintedResolver τ) : TaintedResolver τ := fun tm => do
  let cachedResolvedTainted? ← getCachedResolvedTainted? tm
  if let .hit m := cachedResolvedTainted? then
    return m
  let m? ← f tm
  return m?

mutual

partial def TaintedMeasure.resolve? : TaintedResolver τ := TaintedResolver.memoize fun tm => do
  match tm with
  | .mergeTainted tm1 tm2 _ =>
    let some m1 ← tm1.resolve?
      | let m2? ← tm2.resolve?
        return m2?
    return some m1
  | .taintedConcat tm doc indentation fullness _ =>
    let some m1 ← tm.resolve?
      | return none
    let ms2 ← MeasureSet.resolve doc m1.lastLineLength indentation fullness
    let m2? ← ms2.extractAtMostOne?
    return m2?
  | .concatTainted m1 tm2 _ =>
    let some m2 ← tm2.resolve?
      | return none
    return some <| m1.concat m2
  | .resolveTainted doc columnPos indentation fullness _ =>
    -- TODO: Why resolveCore instead of resolve?
    let ms ← MeasureSet.resolveCore doc columnPos indentation fullness
    let m? ← ms.extractAtMostOne?
    if m?.isNone then
      setCachedFailing doc fullness
    return m?

partial def MeasureSet.extractAtMostOne? (ms : MeasureSet τ) : ResolverM τ (Option (Measure τ)) := do
  match ms with
  | .tainted tm =>
    tm.resolve?
  | .set ms =>
    return ms[0]?

end

def resolve? (doc : CoreDoc) (offset : Nat) : Option (Measure τ) := ResolverM.run do
  let ms1 ← MeasureSet.resolve doc offset 0 {
    isFullBefore := false
    isFullAfter := false
  }
  let ms2 ← MeasureSet.resolve doc offset 0 {
    isFullBefore := false
    isFullAfter := true
  }
  let ms := ms1.merge ms2 (prunable := false)
  ms.extractAtMostOne?

def format? (τ : Type) [Add τ] [LE τ] [DecidableLE τ] [Cost τ]
    (doc : CoreDoc) (offset : Nat) : Option String := do
  let m ← resolve? (τ := τ) doc offset
  return m.print
