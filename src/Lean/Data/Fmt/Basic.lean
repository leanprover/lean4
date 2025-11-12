/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Marc Huisinga
-/
module

prelude
public import Init
public import Std.Data.HashMap.Basic
public import Std.Data.HashSet.Basic
public import Std.Data.Iterators

public section

namespace Lean.Fmt

open Std

def memoHeightLimit : Nat := 0

def nextMemoHeight (memoHeight : Nat) : Nat :=
  if memoHeight = 0 then
    memoHeightLimit
  else
    memoHeight - 1

structure FullnessState where
  isFullBefore : Bool
  isFullAfter : Bool
  deriving BEq, Hashable

abbrev FailureCond := FullnessState → Bool

inductive Doc where
  | failure
  | newline (flattened? : Option String)
  | text (s : String)
  | flatten (d : Doc)
  | indent (n : Nat) (d : Doc)
  | align (d : Doc)
  | reset (d : Doc)
  | full (d : Doc)
  | either (a b : Doc)
  | concat (a b : Doc)
with
  @[computed_field] isFailure : Doc → FailureCond
    | .failure => fun _ => true
    | .newline .. => (·.isFullAfter)
    | .text s => fun
      | { isFullBefore := false, isFullAfter := false } => false
      | { isFullBefore := true, isFullAfter := false } => true
      | { isFullBefore := false, isFullAfter := true } => true
      | { isFullBefore := true, isFullAfter := true } => ! s.isEmpty
    | .full _ => (! ·.isFullAfter)
    | _ => fun _ => false
  @[computed_field] maxNewlineCount? : Doc → Option Nat
    | .failure => none
    | .newline .. => some 1
    | .text _
    | .flatten _ => some 0
    | .indent _ d
    | .align d
    | .reset d
    | .full d => maxNewlineCount? d
    | .either a b => .merge (max · ·) (maxNewlineCount? a) (maxNewlineCount? b)
    | .concat a b => .merge (· + ·) (maxNewlineCount? a) (maxNewlineCount? b)
  @[computed_field] memoHeight : Doc → Nat
    | .failure
    | .newline ..
    | .text _ => memoHeightLimit
    | .flatten d
    | .indent _ d
    | .align d
    | .reset d
    | .full d =>
      let n := memoHeight d
      nextMemoHeight n
    | .either a b
    | .concat a b =>
      let n := min (memoHeight a) (memoHeight b)
      nextMemoHeight n
deriving Inhabited, Repr

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

def Doc.maybeFlattened (d : Doc) : Doc :=
  .either d d.flatten

def Doc.nl : Doc :=
  .newline (some " ")

def Doc.break : Doc :=
  .newline (some "")

def Doc.hardNl : Doc :=
  .newline none

def Doc.oneOf (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .failure
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.either d

def Doc.join (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.concat d

def Doc.joinUsing (sep : Doc) (ds : Array Doc) : Doc :=
  match ds[0]? with
  | none =>
    .text ""
  | some d =>
    ds[1:].foldl (init := d) fun acc d => acc.concat sep |>.concat d

instance : Append Doc where
  append d1 d2 := d1.concat d2

class ToDoc (α : Type) where
  toDoc : α → Doc

instance : ToDoc Doc where
  toDoc d := d

instance : ToDoc String where
  toDoc s := .text s

syntax:max "f'!" interpolatedStr(term) : term

macro_rules
  | `(f'! $interpStr) => do interpStr.expandInterpolatedStr (← `(Doc)) (← `(ToDoc.toDoc))

class Cost (τ : Type) [Add τ] [LE τ] where
  textCost : (columnPos length : Nat) → τ
  newlineCost : (indentationAfterNewline : Nat) → τ
  optimalityCutoffWidth : Nat

class LawfulCost (τ : Type) [Add τ] [LE τ] extends Cost τ, Grind.AddCommMonoid τ, Std.IsLinearOrder τ where
  zero := textCost 0 0

  textCost_columnPos_monotone (cp₁ cp₂ n : Nat) :
    cp₁ ≤ cp₂ → textCost cp₁ n ≤ textCost cp₂ n
  textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    textCost cp (n₁ + n₂) = textCost cp n₁ + textCost (cp + n₁) n₂
  newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ → newlineCost i₁ ≤ newlineCost i₂

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
  while h : i1 < ms1.size do
    r := r.push ms1[i1]
    i1 := i1 + 1
  while h : i2 < ms2.size do
    r := r.push ms2[i2]
    i2 := i2 + 1
  return r

def MeasureSet.Set.dedup (ms : MeasureSet.Set τ) : MeasureSet.Set τ := Id.run do
  let mut deduped := #[]
  let mut i := 0
  while h : i < ms.size - 1 do
    let previous := ms[i]
    let current := ms[i+1]
    -- TODO: Why was this sound again?
    if current.cost <= previous.cost then
      i := i + 1
      continue
    deduped := deduped.push previous
    i := i + 1
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

def getCachedSet? (d : Doc) (columnPos indentation : Nat) (fullness : FullnessState) :
    ResolverM τ (Option (MeasureSet τ)) := do
  return (← get).setCache.get? {
    docPtr := unsafe ptrAddrUnsafe d
    columnPos
    indentation
    fullness
  }

def setCachedSet (d : Doc) (columnPos indentation : Nat) (fullness : FullnessState)
    (set : MeasureSet τ) : ResolverM τ Unit :=
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

def getCachedResolvedTainted? (tm : TaintedMeasure τ) :
    ResolverM τ (CacheResult (Option (Measure τ))) := do
  match (← get).resolvedTaintedCache.get? (unsafe ptrAddrUnsafe tm) with
  | none => return .miss
  | some cached? => return .hit cached?

def setCachedResolvedTainted (tm : TaintedMeasure τ) (m? : Option (Measure τ)) :
    ResolverM τ Unit :=
  modify fun state => { state with
    resolvedTaintedCache := state.resolvedTaintedCache.insert (unsafe ptrAddrUnsafe tm) m?
  }

def isFailing (d : Doc) (fullness : FullnessState) : ResolverM τ Bool := do
  let isCachedFailure := (← get).failureCache.contains {
    docPtr := unsafe ptrAddrUnsafe d
    fullness
  }
  return isCachedFailure || d.isFailure fullness

def setCachedFailing (d : Doc) (fullness : FullnessState) : ResolverM τ Unit :=
  modify fun state => { state with
    failureCache := state.failureCache.insert {
      docPtr := unsafe ptrAddrUnsafe d
      fullness
    }
  }

@[expose] def Resolver (τ : Type) :=
  (d : Doc) → (columnPos indentation : Nat) → (fullness : FullnessState) →
    ResolverM τ (MeasureSet τ)

@[specialize]
def Resolver.memoize (f : Resolver τ) : Resolver τ := fun d columnPos indentation fullness => do
  if ← isFailing d fullness then
    -- TODO: Set failing, unlike Racket impl?
    return .set #[]
  if columnPos > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ
      || ! d.shouldMemoize then
    return ← f d columnPos indentation fullness
  if let some cachedSet ← getCachedSet? d columnPos indentation fullness then
    return cachedSet
  let r ← f d columnPos indentation fullness
  setCachedSet d columnPos indentation fullness r
  return r

mutual

partial def MeasureSet.resolveCore : Resolver τ := fun d columnPos indentation fullness => do
  match d with
  | .failure =>
    return .set #[]
  | .newline .. =>
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
    let set1 ← resolve d columnPos indentation { fullness with isFullAfter := false }
    let set2 ← resolve d columnPos indentation { fullness with isFullAfter := true }
    return .merge set1 set2 (prunable := false)
  | .either d1 d2 =>
    let set1 ← resolve d1 columnPos indentation fullness
    let set2 ← resolve d2 columnPos indentation fullness
    return .merge set1 set2 (prunable := false)
  | .concat d1 d2 =>
    let set1 ← analyzeConcat d d1 d2 columnPos indentation fullness false
    let set2 ← analyzeConcat d d1 d2 columnPos indentation fullness false
    return .merge set1 set2 (prunable := false)
where
  analyzeConcat (d d1 d2 : Doc) (columnPos indentation : Nat) (fullness : FullnessState)
      (isMidFull : Bool) : ResolverM τ (MeasureSet τ) := do
    let fullness1 := { fullness with isFullAfter := isMidFull }
    let fullness2 := { fullness with isFullBefore := isMidFull }
    let set1 ← resolve d1 columnPos indentation fullness1
    match set1 with
    | .tainted tm1 =>
      return .tainted (.taintedConcat tm1 d2 indentation fullness2 d.maxNewlineCount?)
    | .set ms1 =>
      let mut result := .set #[]
      for m1 in ms1 do
        let set2 ← resolve d2 m1.lastLineLength indentation fullness2
        match set2 with
        | .tainted tm2 =>
          return .tainted (.concatTainted m1 tm2 d.maxNewlineCount?)
        | .set ms2 =>
          let m1Result : MeasureSet.Set τ := ms2.map m1.concat
          let m1Result := m1Result.dedup
          result := MeasureSet.merge result (.set m1Result) (prunable := true)
      return result

partial def MeasureSet.resolve : Resolver τ := Resolver.memoize fun d columnPos indentation fullness => do
  let columnPos' :=
    if let .text s := d then
      columnPos + s.length
    else
      columnPos
  if columnPos' > Cost.optimalityCutoffWidth τ || indentation > Cost.optimalityCutoffWidth τ then
    return .tainted (.resolveTainted d columnPos indentation fullness d.maxNewlineCount?)
  return ← resolveCore d columnPos indentation fullness

end

@[expose] def TaintedResolver (τ : Type) :=
    (tm : TaintedMeasure τ) → ResolverM τ (Option (Measure τ))

@[specialize]
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

partial def MeasureSet.extractAtMostOne? (ms : MeasureSet τ) : ResolverM τ (Option (Measure τ)) := do
  match ms with
  | .tainted tm =>
    tm.resolve?
  | .set ms =>
    return ms[0]?

end

def resolve? (d : Doc) (offset : Nat) : Option (Measure τ) := ResolverM.run do
  let ms1 ← MeasureSet.resolve d offset 0 {
    isFullBefore := false
    isFullAfter := false
  }
  let ms2 ← MeasureSet.resolve d offset 0 {
    isFullBefore := false
    isFullAfter := true
  }
  let ms := ms1.merge ms2 (prunable := false)
  ms.extractAtMostOne?

def formatWithCost? (τ : Type) [Add τ] [LE τ] [DecidableLE τ] [Cost τ]
    (d : Doc) (offset : Nat := 0) : Option String := do
  let d := d.preprocess
  let m ← resolve? (τ := τ) d offset
  return m.print

@[grind ext]
structure DefaultCost (softWidth : Nat) (optimalityCutoffWidth : Nat) where
  widthCost : Nat
  heightCost : Nat

def DefaultCost.zero : DefaultCost w W :=
  ⟨0, 0⟩

instance : Zero (DefaultCost w W) where
  zero := DefaultCost.zero

theorem DefaultCost.zero_def : (0 : DefaultCost w W) = ⟨0, 0⟩ := by
  simp only [Zero.zero, OfNat.ofNat, DefaultCost.zero]

def DefaultCost.add (c1 c2 : DefaultCost w W) : DefaultCost w W :=
  ⟨c1.widthCost + c2.widthCost, c1.heightCost + c2.heightCost⟩

instance : Add (DefaultCost w W) where
  add := DefaultCost.add

theorem DefaultCost.add_def {c₁ c₂ : DefaultCost w W} :
    c₁ + c₂ = ⟨c₁.widthCost + c₂.widthCost, c₁.heightCost + c₂.heightCost⟩ := by
  simp only [HAdd.hAdd, Add.add, DefaultCost.add]

theorem DefaultCost.add_zero (c : DefaultCost w W) : c + 0 = c := by
  simp only [zero_def, add_def]
  grind

theorem DefaultCost.add_comm (c₁ c₂ : DefaultCost w W) : c₁ + c₂ = c₂ + c₁ := by
  simp only [add_def]
  grind

theorem DefaultCost.add_assoc (c₁ c₂ c₃ : DefaultCost w W) :
    (c₁ + c₂) + c₃ = c₁ + (c₂ + c₃) := by
  simp only [add_def]
  grind

instance : Grind.AddCommMonoid (DefaultCost w W) where
  zero := DefaultCost.zero
  add_zero := DefaultCost.add_zero
  add_comm := DefaultCost.add_comm
  add_assoc := DefaultCost.add_assoc

def DefaultCost.le
    (c1 c2 : DefaultCost w W) : Bool :=
  if c1.widthCost = c2.widthCost then
    c1.heightCost ≤ c2.heightCost
  else
    c1.widthCost ≤ c2.widthCost

instance : LE (DefaultCost w W) where
  le c1 c2 := DefaultCost.le c1 c2

instance : DecidableLE (DefaultCost w W) := fun _ _ => inferInstanceAs (Decidable (_ = true))

theorem DefaultCost.le_def {c₁ c₂ : DefaultCost w W} :
    c₁ ≤ c₂ ↔
      (if c₁.widthCost = c₂.widthCost then
          c₁.heightCost ≤ c₂.heightCost
        else
          c₁.widthCost ≤ c₂.widthCost) := by
  simp only [LE.le]
  simp [le]

theorem DefaultCost.le_refl (c : DefaultCost w W) : c ≤ c := by
  simp only [le_def]
  grind

theorem DefaultCost.le_trans (c₁ c₂ c₃ : DefaultCost w W) : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃ := by
  simp only [le_def]
  grind

theorem DefaultCost.le_antisymm (c₁ c₂ : DefaultCost w W) : c₁ ≤ c₂ → c₂ ≤ c₁ → c₁ = c₂ := by
  simp only [le_def]
  grind

theorem DefaultCost.le_total (c₁ c₂ : DefaultCost w W) : c₁ ≤ c₂ ∨ c₂ ≤ c₁ := by
  simp only [le_def]
  grind

instance : Std.IsLinearOrder (DefaultCost w W) where
  le_refl := DefaultCost.le_refl
  le_trans := DefaultCost.le_trans
  le_antisymm := DefaultCost.le_antisymm
  le_total := DefaultCost.le_total

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

theorem DefaultCost.textCost_columnPos_monotone
    (cp₁ cp₂ n : Nat) : cp₁ ≤ cp₂ → textCost w W cp₁ n ≤ textCost w W cp₂ n := by
  grind [textCost, = le_def, Nat.mul_le_mul]

theorem DefaultCost.textCost_length_add_decompose (cp n₁ n₂ : Nat) :
    textCost w W cp (n₁ + n₂) = textCost w W cp n₁ + textCost w W (cp + n₁) n₂ := by
  grind [textCost, = add_def, Nat.sub_add_comm]

def DefaultCost.newlineCost (w W _length : Nat) :
    DefaultCost w W :=
  ⟨0, 1⟩

theorem DefaultCost.newlineCost_monotone (i₁ i₂ : Nat) :
    i₁ ≤ i₂ → newlineCost w W i₁ ≤ newlineCost w W i₂ := by
  grind [newlineCost]

def DefaultCost.le_add_invariant (c₁ c₂ c₃ c₄ : DefaultCost w W) : c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄ := by
  grind [= le_def, = add_def]

instance : LawfulCost (DefaultCost softWidth optimalityCutoffWidth) where
  textCost := DefaultCost.textCost softWidth optimalityCutoffWidth
  newlineCost := DefaultCost.newlineCost softWidth optimalityCutoffWidth
  optimalityCutoffWidth := optimalityCutoffWidth

  textCost_columnPos_monotone := DefaultCost.textCost_columnPos_monotone
  textCost_length_add_decompose := DefaultCost.textCost_length_add_decompose
  newlineCost_monotone := DefaultCost.newlineCost_monotone

  le_add_invariant := DefaultCost.le_add_invariant

def format? (d : Doc) (width : Nat)
    (optimalityCutoffWidth : Nat := Nat.max ((5*width)/4) 200)
    (offset : Nat := 0) :
    Option String := do
  formatWithCost? (τ := DefaultCost width optimalityCutoffWidth) d offset
