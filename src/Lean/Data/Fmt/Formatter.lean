/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Lean.Data.Fmt.Basic
public import Std.Data.HashSet.Basic

namespace Lean.Fmt

open Std

def Doc.shouldMemoize (d : Doc) : Bool :=
  d.memoHeight = 0

structure PreprocessingCacheKey where
  docPtr : USize
  isFlattened : Bool
  deriving BEq, Hashable

structure PreprocessingState where
  cache : HashMap PreprocessingCacheKey Doc := {}

def Doc.preprocess (d : Doc) : Doc :=
  goMemoized d false |>.run' {}
where
  goMemoized (d : Doc) (isFlattened : Bool) : StateM PreprocessingState Doc := do
    let cacheKey := { docPtr := unsafe ptrAddrUnsafe d, isFlattened }
    if let some d' := (← get).cache.get? cacheKey then
      return d'
    let d' ← go d isFlattened
    modify fun s => { s with cache := s.cache.insert cacheKey d' }
    return d'
  go (d : Doc) (isFlattened : Bool) : StateM PreprocessingState Doc := do
    match d with
    | .newline flattened? =>
      if isFlattened then
        let some flattened := flattened?
          | return .failure
        return .text flattened
      else
        return .newline none
    | .flatten d =>
      goMemoized d true
    | .failure
    | .text .. =>
      return d
    | .indent n d =>
      let d ← goMemoized d isFlattened
      return .indent n d
    | .align d =>
      let d ← goMemoized d isFlattened
      return .align d
    | .reset d =>
      let d ← goMemoized d isFlattened
      return .reset d
    | .full d =>
      let d ← goMemoized d isFlattened
      return .full d
    | .either d1 d2 =>
      let d1 ← goMemoized d1 isFlattened
      let d2 ← goMemoized d2 isFlattened
      return .either d1 d2
    | .concat d1 d2 =>
      let d1 ← goMemoized d1 isFlattened
      let d2 ← goMemoized d2 isFlattened
      return .concat d1 d2

public class Cost (τ : Type) [Add τ] [LE τ] where
  textCost : (columnPos length : Nat) → τ
  newlineCost : (indentationAfterNewline : Nat) → τ
  optimalityCutoffWidth : Nat

structure Measure (τ : Type) where
  lastLineLength : Nat
  cost : τ
  output : StateM String Unit

variable {τ : Type} [Add τ] [LE τ] [DecidableLE τ] [Cost τ]

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
  | taintedConcat (tm1 : TaintedMeasure τ) (d2 : Doc) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)
  | concatTainted (m1 : Measure τ) (tm2 : TaintedMeasure τ) (maxNewlineCount? : Option Nat)
  | resolveTainted (d : Doc) (columnPos : Nat) (indentation : Nat) (fullness : FullnessState) (maxNewlineCount? : Option Nat)

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

abbrev MeasureSet.Set (τ : Type) := List (Measure τ)

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

inductive MeasureSet (τ : Type) where
  | tainted (tm : TaintedMeasure τ)
  | set (ms : MeasureSet.Set τ)
  deriving Inhabited

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
  isFailureCacheEnabled : Bool := false
  failureCache : HashSet FailureCacheKey := {}

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

inductive CacheResult (α : Type)
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

def enableFailureCache : ResolverM σ τ Unit :=
  modify fun state => { state with
    isFailureCacheEnabled := true
  }

def isFailing (d : Doc) (fullness : FullnessState) : ResolverM σ τ Bool := do
  let s ← get
  let isDocFailure := d.isFailure fullness
  if isDocFailure then
    return true
  else if s.isFailureCacheEnabled then
    let isCachedFailure := (← get).failureCache.contains {
      docPtr := unsafe ptrAddrUnsafe d
      fullness
    }
    return isCachedFailure
  else
    return false

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

@[specialize]
def Resolver.memoize (f : Resolver σ τ) : Resolver σ τ := fun d columnPos indentation fullness => do
  if ← isFailing d fullness then
    -- TODO: Set failing, unlike Racket impl?
    return .set []
  if columnPos > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ
      || ! d.shouldMemoize then
    return ← f d columnPos indentation fullness
  if let some cachedSet ← getCachedSet? d columnPos indentation fullness then
    return cachedSet
  let r ← f d columnPos indentation fullness
  setCachedSet d columnPos indentation fullness r
  return r

mutual

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
  | .flatten _ =>
    -- Eliminated during pre-processing
    unreachable!
  | .indent n d =>
    resolve d columnPos (indentation + n) fullness
  | .align d =>
    resolve d columnPos columnPos fullness
  | .reset d =>
    resolve d columnPos 0 fullness
  | .full d =>
    let set1 ← resolve d columnPos indentation (fullness.setFullAfter false)
    let set2 ← resolve d columnPos indentation (fullness.setFullAfter true)
    return .merge set1 set2 (prunable := false)
  | .either d1 d2 =>
    let set1 ← resolve d1 columnPos indentation fullness
    let set2 ← resolve d2 columnPos indentation fullness
    return .merge set1 set2 (prunable := false)
  | .concat d1 d2 =>
    let set1 ← analyzeConcat d d1 d2 columnPos indentation fullness false
    let set2 ← analyzeConcat d d1 d2 columnPos indentation fullness true
    return .merge set1 set2 (prunable := false)
where
  analyzeConcat (d d1 d2 : Doc) (columnPos indentation : Nat) (fullness : FullnessState)
      (isMidFull : Bool) : ResolverM σ τ (MeasureSet τ) := do
    let fullness1 := fullness.setFullAfter isMidFull
    let fullness2 := fullness.setFullBefore isMidFull
    let set1 ← resolve d1 columnPos indentation fullness1
    match set1 with
    | .tainted tm1 =>
      return .tainted (.taintedConcat tm1 d2 indentation fullness2 d.maxNewlineCount?)
    | .set ms1 =>
      ms1.foldrM (init := MeasureSet.set []) fun m1 acc => do
        let set2 ← resolve d2 m1.lastLineLength indentation fullness2
        let m1Result : MeasureSet τ :=
          match set2 with
          | .tainted tm2 =>
            .tainted (.concatTainted m1 tm2 d.maxNewlineCount?)
          | .set [] =>
            .set []
          | .set (m2 :: ms2) => .set <| Id.run do
            let mut currentBest := m1.concat m2
            let mut deduped := []
            for m2 in ms2 do
              let current := m1.concat m2
              -- TODO: Why was this sound again?
              if current.cost <= currentBest.cost then
                currentBest := current
                continue
              deduped := currentBest :: deduped
              currentBest := current
            return currentBest :: deduped |>.reverse
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
  return m?

mutual

partial def TaintedMeasure.resolve? : TaintedResolver σ τ := TaintedResolver.memoize fun tm => do
  match tm with
  | .mergeTainted tm1 tm2 _ =>
    let some m1 ← tm1.resolve?
      | let m2? ← tm2.resolve?
        return m2?
    return some m1
  | .taintedConcat tm d indentation fullness _ =>
    let some m1 ← tm.resolve?
      | return none
    let ms2 ← MeasureSet.resolve d m1.lastLineLength indentation fullness
    let some m2 ← ms2.extractAtMostOne?
      | return none
    return some <| m1.concat m2
  | .concatTainted m1 tm2 _ =>
    let some m2 ← tm2.resolve?
      | return none
    return some <| m1.concat m2
  | .resolveTainted d columnPos indentation fullness _ =>
    -- TODO: Why resolveCore instead of resolve?
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
  enableFailureCache
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
