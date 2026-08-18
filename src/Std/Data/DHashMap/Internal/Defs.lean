/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro, Markus Himmel
-/
module

prelude
public import Init.Data.Array.Lemmas
public import Std.Data.DHashMap.RawDef
public import Std.Data.Internal.List.Defs
public import Std.Data.DHashMap.Internal.Index
public import Init.Data.Nat.Power2.Basic
import Init.ByCases
import Init.Data.Nat.Power2.Lemmas
import Init.Data.List.Impl
import Init.Omega

public section

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

The table uses open addressing with linear probing. Keys and values live in parallel flat arrays;
`NOption.none` marks an unused cell. Values are stored in `NSigma`, whose key is erased at runtime,
so a cell stores neither a product nor a pointer to a separately allocated entry.

The proof-facing `Raw.buckets` view presents all occupied cells as one associative list. It is used
by the existing list model and is not part of executable hash-map operations.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w w'

variable {α : Type u} {β : α → Type v} {δ : Type w} {m : Type w → Type w'} [Monad m]

namespace Std.DHashMap.Internal

open Std.Internal

@[inline] private def numCellsForCapacity (capacity : Nat) : Nat :=
  (capacity * 4 + 2) / 3

/-- Internal implementation detail of the hash map. -/
def toListModel (buckets : Array (AssocList α β)) : List ((a : α) × β a) :=
  buckets.toList.flatMap AssocList.toList

/-- Internal implementation detail of the hash map. -/
@[inline] def computeSize (buckets : Array (AssocList α β)) : Nat :=
  buckets.foldl (fun d b => d + b.length) 0

end Std.DHashMap.Internal

namespace Std.DHashMap.Internal

/-- A raw table together with the fact that it has at least one cell. -/
abbrev Raw₀ (α : Type u) (β : α → Type v) :=
  { m : Raw α β // 0 < m.keyArray.size }

namespace Raw₀

/-- The result of scanning all occupied cells for a matching key. -/
inductive ScanResult [BEq α] (β : α → Type v) (query : α) (n : Nat) where
  /-- A matching entry was found. -/
  | found (index : Fin n) (key : α) (value : β key) (hmatch : key == query)
  /-- No matching entry exists. -/
  | absent

/-- Scans the physical cells at or after `i` for a matching key. -/
@[expose] def scanFrom [BEq α] (m : Raw₀ α β) (query : α) (i : Nat) :
    ScanResult β query m.1.keyArray.size :=
  if hi : i < m.1.keyArray.size then
    match m.1.entryAtInBounds? i hi with
    | none => scanFrom m query (i + 1)
    | some ⟨k, v⟩ =>
      if h : k == query then .found ⟨i, hi⟩ k v h else scanFrom m query (i + 1)
  else
    .absent
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ hi

/-- Scans the physical cells in index order for a matching key. -/
@[inline] def scanSpec [BEq α] (m : Raw₀ α β) (query : α) :
    ScanResult β query m.1.keyArray.size :=
  scanFrom m query 0

/-- The result of probing a table. -/
inductive ProbeResult [BEq α] (β : α → Type v) (query : α) (n : Nat) where
  /-- A matching entry was found. -/
  | found (index : Fin n) (key : α) (value : β key) (hmatch : key == query)
  /-- The first tombstone, or otherwise the first unused cell, in the probe sequence. -/
  | empty (index : Fin n)
  /-- Every cell was inspected without finding a match or an unused cell. -/
  | full

/-- Advances one cell, wrapping at the end of the table. -/
@[inline] def nextIndex {n : Nat} (hn : 0 < n) (i : Fin n) : Fin n :=
  if h : i.1 + 1 < n then ⟨i.1 + 1, h⟩ else ⟨0, hn⟩

/-- The natural-number component of the next position in a probe sequence. -/
@[inline] def nextIndexNat (n i : Nat) : Nat :=
  if i + 1 < n then i + 1 else 0

/-- The initial probe position, expressed without a dependent bound proof. -/
@[inline] def probeStart (n : Nat) (hash : UInt64) : Nat :=
  if h : 0 < n then (mkIdx n h hash).1.toNat else 0

/-- `probeStart` agrees with the bounded index used by executable probing. -/
@[simp] theorem probeStart_eq_mkIdx {n : Nat} (hn : 0 < n) (hash : UInt64) :
    probeStart n hash = (mkIdx n hn hash).1.toNat := by
  simp only [probeStart, hn, ↓reduceDIte]

/-- The two representations of the next probe position agree. -/
@[simp] theorem nextIndex_val {n : Nat} (hn : 0 < n) (i : Fin n) :
    (nextIndex hn i).1 = nextIndexNat n i.1 := by
  unfold nextIndex nextIndexNat
  split <;> rfl

/-- A sequence of occupied key cells connecting two positions in a probe sequence. -/
inductive ProbePath (keys : Array (NOption α)) : Nat → Nat → Nat → Prop where
  /-- The target is the current cell. -/
  | here (fuel : Nat) (i : Nat) (hi : i < keys.size) : ProbePath keys (fuel + 1) i i
  /-- The current key cell is occupied and the target is reachable from the next cell. -/
  | next {fuel i target : Nat} (hi : i < keys.size) (hkey : keys[i] ≠ .none)
      (path : ProbePath keys fuel (nextIndexNat keys.size i) target) :
      ProbePath keys (fuel + 1) i target

/-- Probes from `i`, retaining the first tombstone as a possible insertion cell. -/
@[specialize, expose]
def probeFromAux [BEq α] (m : @& Raw₀ α β) (query : α) :
    Option (Fin m.1.keyArray.size) →
      (fuel i : Nat) → i < m.1.keyArray.size → ProbeResult β query m.1.keyArray.size
  | firstEmpty, 0, _, _ =>
    match firstEmpty with
    | none => .full
    | some index => .empty index
  | firstEmpty, fuel + 1, i, hi =>
    match m.1.keyArray[i] with
    | .none =>
      match firstEmpty with
      | none => .empty ⟨i, hi⟩
      | some index => .empty index
    | .some _ =>
      match m.1.entryAtInBounds? i hi with
      | none =>
        let firstEmpty :=
          match firstEmpty with
          | none => some ⟨i, hi⟩
          | some index => some index
        let next := nextIndex m.2 ⟨i, hi⟩
        probeFromAux m query firstEmpty fuel next.1 next.2
      | some ⟨k, v⟩ =>
        if h : k == query then
          .found ⟨i, hi⟩ k v h
        else
          let next := nextIndex m.2 ⟨i, hi⟩
          probeFromAux m query firstEmpty fuel next.1 next.2

/-- Probes from `i` until it finds the key or a cell suitable for insertion. -/
@[inline, expose] def probeFrom [BEq α] (m : @& Raw₀ α β) (query : α)
    (fuel i : Nat) (hi : i < m.1.keyArray.size) : ProbeResult β query m.1.keyArray.size :=
  probeFromAux m query none fuel i hi

/-- Probes consecutive cells until it finds the key or an unused cell. -/
@[specialize] def probe [BEq α] [Hashable α] (m : @& Raw₀ α β) (query : α) :
    ProbeResult β query m.1.keyArray.size :=
  let start := mkIdx m.1.keyArray.size m.2 (hash query)
  probeFrom m query m.1.keyArray.size start.1.toNat start.2

private theorem probeFromAux_found_cell [BEq α] (m : Raw₀ α β) (query : α)
    (firstEmpty : Option (Fin m.1.keyArray.size)) (fuel i : Nat)
    (hi : i < m.1.keyArray.size) (index : Fin m.1.keyArray.size)
    (k : α) (v : β k) (hmatch : k == query)
    (h : m.probeFromAux query firstEmpty fuel i hi = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  induction fuel generalizing firstEmpty i with
  | zero =>
    simp only [probeFromAux] at h
    cases firstEmpty <;> contradiction
  | succ fuel ih =>
    rw [probeFromAux.eq_def] at h
    cases hk : m.1.keyArray[i] with
    | none =>
      simp only [hk] at h
      cases firstEmpty <;> contradiction
    | some key =>
      simp only [hk] at h
      cases he : m.1.entryAtInBounds? i hi with
      | none =>
        simp only [he] at h
        cases hf : firstEmpty with
        | none =>
          simp only [hf] at h
          exact ih (some ⟨i, hi⟩) _ _ h
        | some first =>
          simp only [hf] at h
          exact ih (some first) _ _ h
      | some p =>
        rcases p with ⟨k', v'⟩
        simp only [he] at h
        split at h
        · cases h
          exact he
        · exact ih firstEmpty _ _ h

private theorem probe_found_cell [BEq α] [Hashable α] (m : Raw₀ α β) (query : α)
    (index : Fin m.1.keyArray.size) (k : α) (v : β k) (hmatch : k == query)
    (h : m.probe query = .found index k v hmatch) :
    m.1.entryAtInBounds? index.1 index.2 = some ⟨k, v⟩ := by
  unfold probe at h
  exact probeFromAux_found_cell m query none _ _ _ index k v hmatch h

/-- Searches the physical table for a matching key. -/
@[specialize] def scan [BEq α] [Hashable α] (m : @& Raw₀ α β) (query : α) :
    ScanResult β query m.1.keyArray.size :=
  match m.probe query with
  | .found i k v h => .found i k v h
  | .empty .. | .full => .absent

/-- The result of searching the physical table for an unused cell. -/
inductive EmptyResult (n : Nat) where
  /-- An unused cell was found. -/
  | empty (index : Fin n)
  /-- Every cell is occupied. -/
  | full

/-- Searches cells at or after `i` for an unused cell. -/
@[expose] def findEmptyFrom (m : @& Raw₀ α β) (i : Nat) : EmptyResult m.1.keyArray.size :=
  if hi : i < m.1.keyArray.size then
    match m.1.entryAtInBounds? i hi with
    | none => .empty ⟨i, hi⟩
    | some _ => findEmptyFrom m (i + 1)
  else
    .full
termination_by m.1.keyArray.size - i
decreasing_by all_goals exact Nat.sub_succ_lt_self _ _ hi

/-- Searches the physical table for an unused cell. -/
@[inline] def findEmpty (m : @& Raw₀ α β) : EmptyResult m.1.keyArray.size :=
  findEmptyFrom m 0

/-- Allocates the key cells for an empty table. -/
@[noinline, simp] def emptyKeyArray (cellCount : Nat) : Array (NOption α) :=
  Array.replicate cellCount .none

/-- Allocates the value cells for an empty table. -/
@[noinline, simp] def emptyValueArray (cellCount : Nat) : Array (NOption (NSigma β)) :=
  Array.replicate cellCount .none

/-- Constructs an empty table with an explicitly specified positive cell count. -/
@[inline, expose] def emptyWithCellCount (cellCount : Nat) (h : 0 < cellCount) : Raw₀ α β :=
  ⟨{ size := 0,
      keyArray := emptyKeyArray cellCount,
      valueArray := emptyValueArray cellCount,
      keysValues := by
        simpa [emptyKeyArray, emptyValueArray] using
          (Raw.keysValues_replicate (n := cellCount) (α := α) (β := β)) },
    by simpa [emptyKeyArray]⟩

/-- Internal implementation detail of the hash map. -/
@[inline] def emptyWithCapacity (capacity := 8) : Raw₀ α β :=
  let cellCount := (numCellsForCapacity capacity).nextPowerOfTwo
  emptyWithCellCount cellCount <| by
    simpa [cellCount] using Nat.pos_of_isPowerOfTwo (Nat.isPowerOfTwo_nextPowerOfTwo _)

/-- Writes an entry into a table without growing it. -/
@[inline] def insertNoExpand [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Raw₀ α β :=
  match m.probe a with
  | .found i _ _ _ =>
    ⟨m.1.setEntry m.1.size i.1 i.2 a b, by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .empty i =>
    ⟨m.1.setEntry (m.1.size + 1) i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .full =>
    match m.findEmpty with
    | .empty i =>
      ⟨m.1.setEntry (m.1.size + 1) i.1 i.2 a b,
        by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
    | .full => m

/-- Copies all entries into a table with twice as many cells. -/
def expand [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  let cellCount := m.1.keyArray.size * 2
  let target : Raw₀ α β := emptyWithCellCount cellCount (Nat.mul_pos m.2 Nat.two_pos)
  m.1.fold (fun target k v => target.insertNoExpand k v) target

/-- Rebuilds the table at its current cell count, discarding tombstones. -/
def compact [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  let target : Raw₀ α β := emptyWithCellCount m.1.keyArray.size m.2
  m.1.fold (fun target k v => target.insertNoExpand k v) target

/-- Grows the table before an insertion that would exceed a load factor of 0.75. -/
@[inline] def expandIfNecessary [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  if m.1.size + 1 < m.1.keyArray.size ∧
      (m.1.size + 1) * 4 ≤ m.1.keyArray.size * 3 then m else m.expand

/-- Inserts a known-new mapping at an available cell, growing the table when necessary. -/
@[inline] def insertNewAt [BEq α] [Hashable α] (m : Raw₀ α β)
    (i : Fin m.1.keyArray.size) (a : α) (b : β a) : Raw₀ α β :=
  if m.1.size + 1 < m.1.keyArray.size ∧
      (m.1.size + 1) * 4 ≤ m.1.keyArray.size * 3 then
    ⟨m.1.setEntry (m.1.size + 1) i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  else
    m.expand.insertNoExpand a b

/-- Proof-facing insertion definition. -/
noncomputable def insert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  match m.scan a with
  | .found i _ _ _ =>
    ⟨m.1.setEntry m.1.size i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .absent => m.expandIfNecessary.insertNoExpand a b

/-- Single-probe insertion used by compiled code. -/
@[inline] def insertImpl [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Raw₀ α β :=
  match m.probe a with
  | .found i _ _ _ =>
    ⟨m.1.setEntry m.1.size i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .empty i => m.insertNewAt i a b
  | .full => m.expandIfNecessary.insertNoExpand a b

@[csimp] theorem insert_eq_insertImpl : @insert = @insertImpl := by
  funext α β instBEq instHashable m a b
  unfold insert insertImpl scan
  cases hp : m.probe a with
  | found => simp
  | empty =>
    simp only
    unfold insertNewAt expandIfNecessary
    split <;> simp_all [insertNoExpand]
  | full => simp

/-- Internal implementation detail of the hash map. -/
@[implicit_reducible] def contains [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  match m.scan a with
  | .found .. => true
  | .absent => false

/-- Internal implementation detail of the hash map. -/
def getEntry? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    Option ((k : α) × β k) :=
  match m.scan a with
  | .found _ k v _ => some ⟨k, v⟩
  | .absent => none

/-- Internal implementation detail of the hash map. -/
def getEntry [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (hma : m.contains a) :
    (k : α) × β k :=
  (m.getEntry? a).get <| by
    unfold getEntry?
    cases h : m.scan a with
    | found => rfl
    | absent => simp [contains, h] at hma

/-- Internal implementation detail of the hash map. -/
def get? [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  match m.scan a with
  | .found _ _ v h => some <| cast (congrArg β (eq_of_beq h)) v
  | .absent => none

/-- Internal implementation detail of the hash map. -/
@[irreducible, inline] def get [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β)
    (a : α) (hma : m.contains a) :
    β a :=
  (m.get? a).get <| by
    unfold get?
    cases h : m.scan a with
    | found => rfl
    | absent => simp [contains, h] at hma

/-- Internal implementation detail of the hash map. -/
def getEntryD [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (fallback : (k : α) × β k) : (k : α) × β k :=
  (m.getEntry? a).getD fallback

/-- Internal implementation detail of the hash map. -/
def getEntry! [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    [Inhabited ((k : α) × β k)] : (k : α) × β k :=
  (m.getEntry? a).getD default

/-- Internal implementation detail of the hash map. -/
def getD [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : β a) :
    β a :=
  (m.get? a).getD fallback

/-- Internal implementation detail of the hash map. -/
def get! [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] :
    β a :=
  match m.get? a with
  | some v => v
  | none => panic! "key is not present in hash table"

/-- Periodically rebuilds a table after deletion so tombstones cannot accumulate indefinitely. -/
@[inline] def compactAfterErase [BEq α] [Hashable α] (m : Raw₀ α β) : Raw₀ α β :=
  if m.1.size == 0 || m.1.size.nextPowerOfTwo == m.1.size then m.compact else m

/-- Removes the entry matching `a` without rebuilding the table. -/
def eraseNoCompact [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  match m.scan a with
  | .found i _ _ _ =>
    ⟨m.1.clearCell (m.1.size - 1) i i.isLt,
      by simpa [Raw.clearCell, Raw.setCell] using m.2⟩
  | .absent => m

/-- Removes the entry matching `a`, if present. -/
def erase [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  match m.scan a with
  | .found i _ _ _ =>
    let erased : Raw₀ α β :=
      ⟨m.1.clearCell (m.1.size - 1) i i.isLt,
        by simpa [Raw.clearCell, Raw.setCell] using m.2⟩
    erased.compactAfterErase
  | .absent => m

/-- Internal implementation detail of the hash map. -/
@[specialize] noncomputable def modify [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : β a → β a) : Raw₀ α β :=
  match m.get? a with
  | .none => m
  | .some v => m.insert a (f v)

/-- Updates a value in a cell whose key is known to match the query. -/
@[inline] def setValueForQuery [BEq α] [LawfulBEq α] (m : Raw₀ α β)
    (i : Fin m.1.keyArray.size) (a : α) (b : β a) : Raw₀ α β :=
  let cell : { key // m.1.keyArray[i] = key } := ⟨m.1.keyArray[i], rfl⟩
  match cell with
  | ⟨.none, _⟩ => m
  | ⟨.some k, hkey⟩ =>
    if h : k == a then
      let b' := cast (congrArg β (eq_of_beq h).symm) b
      ⟨m.1.setValue m.1.size i.1 i.2 k hkey b',
        by simpa [Raw.setValue] using m.2⟩
    else
      m

theorem setEntry_eq_setValueForQuery [BEq α] [LawfulBEq α] (m : Raw₀ α β)
    (i : Fin m.1.keyArray.size) (a : α) (hkey : m.1.keyArray[i] = .some a) (b : β a) :
    (⟨m.1.setEntry m.1.size i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩ : Raw₀ α β) =
      m.setValueForQuery i a b := by
  simp [setValueForQuery, hkey]
  exact Raw.setEntry_eq_setValue m.1 m.1.size i.1 i.2 a hkey b

/-- Single-probe implementation of `modify`. -/
@[specialize, inline] def modifyImpl [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (f : β a → β a) : Raw₀ α β :=
  match m.probe a with
  | .found i _ v h =>
    let v' := f (cast (congrArg β (eq_of_beq h)) v)
    m.setValueForQuery i a v'
  | .empty .. | .full => m

/-- Internal implementation detail of the hash map. -/
@[specialize] noncomputable def alter [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : Option (β a) → Option (β a)) : Raw₀ α β :=
  match m.get? a with
  | .none =>
    match f none with
    | .none => m
    | .some v => m.insert a v
  | .some v =>
    match f (some v) with
    | .none => m.erase a
    | .some v' => m.insert a v'

/-- Single-probe implementation of `alter`. -/
@[specialize, inline] def alterImpl [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (f : Option (β a) → Option (β a)) : Raw₀ α β :=
  match m.probe a with
  | .found i _ v h =>
    match f (some (cast (congrArg β (eq_of_beq h)) v)) with
    | none =>
      let erased : Raw₀ α β :=
        ⟨m.1.clearCell (m.1.size - 1) i.1 i.2,
          by simpa [Raw.clearCell, Raw.setCell] using m.2⟩
      erased.compactAfterErase
    | some v' =>
      m.setValueForQuery i a v'
  | .empty i =>
    match f none with
    | none => m
    | some v => m.insertNewAt i a v
  | .full =>
    match f none with
    | none => m
    | some v => m.expandIfNecessary.insertNoExpand a v

/-- Checks membership and inserts a replacement in one operation. -/
@[irreducible] noncomputable def containsThenInsert [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : Bool × Raw₀ α β :=
  (m.contains a, m.insert a b)

/-- Single-probe implementation of `containsThenInsert`. -/
@[inline] def containsThenInsertImpl [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : Bool × Raw₀ α β :=
  match m.probe a with
  | .found i _ _ _ =>
    (true, ⟨m.1.setEntry m.1.size i.1 i.2 a b,
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩)
  | .empty i => (false, m.insertNewAt i a b)
  | .full => (false, m.expandIfNecessary.insertNoExpand a b)

/-- Checks membership and inserts only when absent. -/
noncomputable def containsThenInsertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : Bool × Raw₀ α β :=
  if m.contains a then (true, m) else (false, m.insert a b)

/-- Single-probe implementation of `containsThenInsertIfNew`. -/
@[inline] def containsThenInsertIfNewImpl [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : Bool × Raw₀ α β :=
  match m.probe a with
  | .found .. => (true, m)
  | .empty i => (false, m.insertNewAt i a b)
  | .full => (false, m.expandIfNecessary.insertNoExpand a b)

/-- Inserts only when no matching key is present. -/
noncomputable def insertIfNew [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Raw₀ α β :=
  if m.contains a then m else m.insert a b

/-- Single-probe implementation of `insertIfNew`. -/
@[inline] def insertIfNewImpl [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    Raw₀ α β :=
  match m.probe a with
  | .found .. => m
  | .empty i => m.insertNewAt i a b
  | .full => m.expandIfNecessary.insertNoExpand a b

/-- Retrieves an existing value, or inserts the supplied value when absent. -/
@[irreducible] noncomputable def getThenInsertIfNew? [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (b : β a) : Option (β a) × Raw₀ α β :=
  (m.get? a, m.insertIfNew a b)

/-- Single-probe implementation of `getThenInsertIfNew?`. -/
@[inline] def getThenInsertIfNewImpl? [BEq α] [Hashable α] [LawfulBEq α]
    (m : Raw₀ α β) (a : α) (b : β a) : Option (β a) × Raw₀ α β :=
  match m.probe a with
  | .found _ _ v h => (some (cast (congrArg β (eq_of_beq h)) v), m)
  | .empty i => (none, m.insertNewAt i a b)
  | .full => (none, m.expandIfNecessary.insertNoExpand a b)

@[csimp] theorem modify_eq_modifyImpl : @modify = @modifyImpl := by
  funext α β instBEq instHashable instLawfulBEq m a f
  cases hp : m.probe a with
  | found i k v h =>
    have hentry := probe_found_cell m a i k v h hp
    have hkey := Raw.keyArray_eq_some_of_entryAtInBounds_eq_some m.1 i i.isLt k v hentry
    have hka : k = a := eq_of_beq h
    subst a
    simpa [modify, modifyImpl, get?, scan, hp, insert_eq_insertImpl, insertImpl] using
      setEntry_eq_setValueForQuery m i k hkey (f v)
  | empty | full =>
    simp [modify, modifyImpl, get?, scan, hp]

@[csimp] theorem alter_eq_alterImpl : @alter = @alterImpl := by
  funext α β instBEq instHashable instLawfulBEq m a f
  cases hp : m.probe a with
  | found i k v h =>
    have hentry := probe_found_cell m a i k v h hp
    have hkey := Raw.keyArray_eq_some_of_entryAtInBounds_eq_some m.1 i i.isLt k v hentry
    have hka : k = a := eq_of_beq h
    subst a
    cases hf : f (some v) with
    | none =>
      simp [alter, alterImpl, get?, erase, scan, hp, hf]
    | some v' =>
      simpa [alter, alterImpl, get?, erase, scan, hp, hf,
        insert_eq_insertImpl, insertImpl] using
        setEntry_eq_setValueForQuery m i k hkey v'
  | empty | full =>
    simp [alter, alterImpl, get?, scan, hp, insert_eq_insertImpl, insertImpl]

@[csimp] theorem containsThenInsert_eq_containsThenInsertImpl :
    @containsThenInsert = @containsThenInsertImpl := by
  funext α β instBEq instHashable m a b
  unfold containsThenInsert containsThenInsertImpl contains scan
  rw [insert_eq_insertImpl]
  cases hp : m.probe a <;> simp [hp, insertImpl]

@[csimp] theorem containsThenInsertIfNew_eq_containsThenInsertIfNewImpl :
    @containsThenInsertIfNew = @containsThenInsertIfNewImpl := by
  funext α β instBEq instHashable m a b
  unfold containsThenInsertIfNew containsThenInsertIfNewImpl contains scan
  rw [insert_eq_insertImpl]
  cases hp : m.probe a <;> simp [hp, insertImpl]

@[csimp] theorem insertIfNew_eq_insertIfNewImpl : @insertIfNew = @insertIfNewImpl := by
  funext α β instBEq instHashable m a b
  unfold insertIfNew insertIfNewImpl contains scan
  rw [insert_eq_insertImpl]
  cases hp : m.probe a <;> simp [hp, insertImpl]

@[csimp] theorem getThenInsertIfNew_eq_getThenInsertIfNewImpl :
    @getThenInsertIfNew? = @getThenInsertIfNewImpl? := by
  funext α β instBEq instHashable instLawfulBEq m a b
  unfold getThenInsertIfNew? getThenInsertIfNewImpl? get? scan
  cases hp : m.probe a <;>
    simp [hp, insertIfNew, contains, scan, insert_eq_insertImpl, insertImpl]

/-- Invariants carried by a `filterMap` target. -/
structure FilterMapTargetValid {γ : α → Type w} (m : Raw₀ α β) (t : Raw₀ α γ) : Prop where
  /-- The target has the same number of cells as the source. -/
  size_eq : t.1.keyArray.size = m.1.keyArray.size
  /-- The target's parallel arrays are aligned. -/
  keysValues : Raw.KeysValues t.1.keyArray t.1.valueArray
  /-- The target reuses the source key array. -/
  keyArray_eq : t.1.keyArray = m.1.keyArray

/-- A `filterMap` target with the source layout and aligned key and value cells. -/
abbrev FilterMapTarget {γ : α → Type w} (m : Raw₀ α β) :=
  { t : Raw₀ α γ // FilterMapTargetValid m t }

/-- Transforms one physical cell, updating only the target value array. -/
@[expose] def filterMapStep {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β)
    (target : FilterMapTarget (γ := γ) m)
    (i : Nat) (hi : i < m.1.keyArray.size) :
    FilterMapTarget (γ := γ) m :=
  match hkey : m.1.keyArray[i] with
  | .none => target
  | .some k =>
    have hiv : i < m.1.valueArray.size := by simpa [m.1.keysValues.1] using hi
    match hvalue : m.1.valueArray[i] with
    | .none => target
    | .some v =>
      have hfst : v.fst = k := by
        have hcell := m.1.keysValues.2 i hi hiv
        rw [hkey, hvalue] at hcell
        exact hcell
      match f k (hfst ▸ v.snd) with
      | .none => target
      | .some w =>
        have hiTarget : i < target.1.1.keyArray.size := by
          simpa [target.2.1] using hi
        have htargetKey : target.1.1.keyArray[i] = .some k := by
          simpa [target.2.3] using hkey
        let next : Raw₀ α γ :=
          ⟨target.1.1.setValue (target.1.1.size + 1) i hiTarget k htargetKey w,
            by simpa [Raw.setValue] using target.1.2⟩
        ⟨next, by
          refine ⟨?_, next.1.keysValues, ?_⟩
          · simpa [next, Raw.setValue] using target.2.1
          · simpa [next, Raw.setValue] using target.2.3⟩

/-- Transforms physical cells at or after `i`. -/
@[expose] def filterMapLoop {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β)
    (target : FilterMapTarget (γ := γ) m)
  (i : Nat) : FilterMapTarget (γ := γ) m :=
  if hi : i < m.1.keyArray.size then
    filterMapLoop f m (filterMapStep f m target i hi) (i + 1)
  else
    target
termination_by m.1.keyArray.size - i
decreasing_by exact Nat.sub_succ_lt_self _ _ hi

/-- Constructs the all-empty value array used as the target of `filterMap`. -/
@[inline, expose] def filterMapTarget {γ : α → Type w} (m : Raw₀ α β) :
    FilterMapTarget (γ := γ) m :=
  ⟨⟨{ size := 0,
        keyArray := m.1.keyArray,
        valueArray := Array.replicate m.1.keyArray.size .none,
        keysValues := Raw.keysValues_replicateValuesNone m.1.keyArray }, m.2⟩,
    rfl, Raw.keysValues_replicateValuesNone m.1.keyArray, rfl⟩

/-- Updates and optionally removes values. -/
@[specialize] def filterMap {γ : α → Type w} (f : (a : α) → β a → Option (γ a))
    (m : Raw₀ α β) : Raw₀ α γ :=
  (filterMapLoop f m (filterMapTarget m) 0).1

/-- Updates all values. -/
@[specialize, expose] def map {γ : α → Type w} (f : (a : α) → β a → γ a) (m : Raw₀ α β) :
    Raw₀ α γ :=
  m.filterMap fun k v => some (f k v)

/-- Removes mappings that do not satisfy `f`. -/
@[specialize] def filter (f : (a : α) → β a → Bool) (m : Raw₀ α β) : Raw₀ α β :=
  m.filterMap fun k v => if f k v then some v else none

/-- Inserts every mapping yielded by `l`. -/
def insertMany {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] [BEq α] [Hashable α]
    (m : Raw₀ α β) (l : ρ) : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } :=
    ⟨m, fun _ _ => id⟩
  for ⟨a, b⟩ in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Erases the key of every mapping yielded by `l`. -/
def eraseManyEntries {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] [BEq α] [Hashable α]
    (m : Raw₀ α β) (l : ρ) : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a}, P m'' → P (m''.erase a)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a}, P m'' → P (m''.erase a)) → P m → P m' } :=
    ⟨m, fun _ _ => id⟩
  for ⟨a, _⟩ in l do
    r := ⟨r.1.erase a, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Inserts every previously absent mapping yielded by `l`. -/
@[inline] def insertManyIfNew {ρ : Type w} [ForIn Id ρ ((a : α) × β a)] [BEq α]
    [Hashable α] (m : Raw₀ α β) (l : ρ) : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α β // ∀ (P : Raw₀ α β → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } :=
    ⟨m, fun _ _ => id⟩
  for ⟨a, b⟩ in l do
    r := ⟨r.1.insertIfNew a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Internal implementation detail of the hash map. -/
@[inline] def interSmallerFn [BEq α] [Hashable α] (m sofar : Raw₀ α β) (k : α) : Raw₀ α β :=
  match m.getEntry? k with
  | some kv => sofar.insert kv.1 kv.2
  | none => sofar

/-- Internal implementation detail of the hash map. -/
def interSmaller [BEq α] [Hashable α] (m₁ : Raw₀ α β) (m₂ : Raw α β) : Raw₀ α β :=
  m₂.fold (fun sofar k _ => interSmallerFn m₁ sofar k) emptyWithCapacity

/-- Internal implementation detail of the hash map. -/
@[inline] def union [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) : Raw₀ α β :=
  if m₁.1.size ≤ m₂.1.size then (m₂.insertManyIfNew m₁.1).1 else (m₁.insertMany m₂.1).1

/-- Internal implementation detail of the hash map. -/
def inter [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) : Raw₀ α β :=
  if m₁.1.size ≤ m₂.1.size then m₁.filter fun k _ => m₂.contains k
  else interSmaller m₁ m₂.1

/-- Internal implementation detail of the hash map. -/
def beq [BEq α] [LawfulBEq α] [Hashable α] [∀ k, BEq (β k)] (m₁ m₂ : Raw₀ α β) : Bool :=
  if m₁.1.size != m₂.1.size then false else m₁.1.all fun k v => m₂.get? k == some v

/-- Internal implementation detail of the hash map. -/
@[inline] def diff [BEq α] [Hashable α] (m₁ m₂ : Raw₀ α β) : Raw₀ α β :=
  if m₁.1.size ≤ m₂.1.size then m₁.filter fun k _ => !m₂.contains k
  else (eraseManyEntries m₁ m₂.1).1

namespace Const

variable {β : Type v}

/-- Internal implementation detail of the hash map. -/
def get? [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  match m.scan a with
  | .found _ _ v _ => some v
  | .absent => none

/-- Internal implementation detail of the hash map. -/
@[irreducible, inline] def get [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (a : α) (hma : m.contains a) : β :=
  (get? m a).get <| by
    unfold get?
    cases h : m.scan a with
    | found => rfl
    | absent => simp [Raw₀.contains, h] at hma

/-- Internal implementation detail of the hash map. -/
def getD [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fallback : β) : β :=
  (get? m a).getD fallback

/-- Internal implementation detail of the hash map. -/
def get! [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) : β :=
  match get? m a with
  | some v => v
  | none => panic! "key is not present in hash table"

/-- Internal implementation detail of the hash map. -/
@[specialize] noncomputable def modify [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : β → β) : Raw₀ α (fun _ => β) :=
  match get? m a with
  | .none => m
  | .some v => m.insert a (f v)

/-- Single-probe implementation of `Const.modify`. -/
@[specialize, inline] def modifyImpl [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (a : α) (f : β → β) : Raw₀ α (fun _ => β) :=
  match m.probe a with
  | .found i _ v _ =>
    ⟨m.1.setEntry m.1.size i.1 i.2 a (f v),
      by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .empty .. | .full => m

/-- Internal implementation detail of the hash map. -/
@[specialize] noncomputable def alter [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : Option β → Option β) : Raw₀ α (fun _ => β) :=
  match get? m a with
  | .none =>
    match f none with
    | .none => m
    | .some v => m.insert a v
  | .some v =>
    match f (some v) with
    | .none => m.erase a
    | .some v' => m.insert a v'

/-- Single-probe implementation of `Const.alter`. -/
@[specialize, inline] def alterImpl [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (a : α) (f : Option β → Option β) :
    Raw₀ α (fun _ => β) :=
  match m.probe a with
  | .found i _ v _ =>
    match f (some v) with
    | none =>
      let erased : Raw₀ α (fun _ => β) :=
        ⟨m.1.clearCell (m.1.size - 1) i.1 i.2,
          by simpa [Raw.clearCell, Raw.setCell] using m.2⟩
      erased.compactAfterErase
    | some v' =>
      ⟨m.1.setEntry m.1.size i.1 i.2 a v',
        by simpa [Raw.setEntry, Raw.setCell] using m.2⟩
  | .empty i =>
    match f none with
    | none => m
    | some v => m.insertNewAt i a v
  | .full =>
    match f none with
    | none => m
    | some v => m.expandIfNecessary.insertNoExpand a v

/-- Retrieves an existing value, or inserts the supplied value when absent. -/
@[irreducible] noncomputable def getThenInsertIfNew? [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (a : α)
    (b : β) : Option β × Raw₀ α (fun _ => β) :=
  (get? m a, m.insertIfNew a b)

/-- Single-probe implementation of `Const.getThenInsertIfNew?`. -/
@[inline] def getThenInsertIfNewImpl? [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (a : α)
    (b : β) : Option β × Raw₀ α (fun _ => β) :=
  match m.probe a with
  | .found _ _ v _ => (some v, m)
  | .empty i => (none, m.insertNewAt i a b)
  | .full => (none, m.expandIfNecessary.insertNoExpand a b)

@[csimp] theorem modify_eq_modifyImpl : @modify = @modifyImpl := by
  funext α β instBEq instHashable m a f
  unfold modify modifyImpl get? Raw₀.scan
  rw [Raw₀.insert_eq_insertImpl]
  cases hp : m.probe a <;> simp [hp, Raw₀.insertImpl]

@[csimp] theorem alter_eq_alterImpl : @alter = @alterImpl := by
  funext α β instBEq instHashable m a f
  unfold alter alterImpl get? Raw₀.erase Raw₀.scan
  rw [Raw₀.insert_eq_insertImpl]
  cases hp : m.probe a <;> simp [hp, Raw₀.insertImpl]

@[csimp] theorem getThenInsertIfNew_eq_getThenInsertIfNewImpl :
    @getThenInsertIfNew? = @getThenInsertIfNewImpl? := by
  funext α β instBEq instHashable m a b
  unfold getThenInsertIfNew? getThenInsertIfNewImpl? get? Raw₀.scan
  cases hp : m.probe a <;>
    simp [hp, Raw₀.insertIfNew, Raw₀.contains, Raw₀.scan,
      Raw₀.insert_eq_insertImpl, Raw₀.insertImpl]

/-- Inserts every pair yielded by `l`. -/
def insertMany {ρ : Type w} [ForIn Id ρ (α × β)] [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => β)) (l : ρ) :
    { m' : Raw₀ α (fun _ => β) // ∀ (P : Raw₀ α (fun _ => β) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α (fun _ => β) // ∀ (P : Raw₀ α (fun _ => β) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insert a b)) → P m → P m' } :=
    ⟨m, fun _ _ => id⟩
  for (a, b) in l do
    r := ⟨r.1.insert a b, fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Inserts every previously absent key yielded by `l`. -/
def insertManyIfNewUnit {ρ : Type w} [ForIn Id ρ α] [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => Unit)) (l : ρ) :
    { m' : Raw₀ α (fun _ => Unit) // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } := Id.run do
  let mut r : { m' : Raw₀ α (fun _ => Unit) // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m' } :=
    ⟨m, fun _ _ => id⟩
  for a in l do
    r := ⟨r.1.insertIfNew a (), fun _ h hm => h (r.2 _ h hm)⟩
  return r

/-- Internal implementation detail of the hash map. -/
def beq [BEq α] [Hashable α] [BEq β] (m₁ m₂ : Raw₀ α (fun _ => β)) : Bool :=
  if m₁.1.size != m₂.1.size then false else m₁.1.all fun k v => get? m₂ k == some v

end Const

/-- Internal implementation detail of the hash map. -/
def getKey? [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option α :=
  match m.scan a with
  | .found _ k _ _ => some k
  | .absent => none

/-- Internal implementation detail of the hash map. -/
@[irreducible, inline] def getKey [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (hma : m.contains a) : α :=
  (m.getKey? a).get <| by
    unfold getKey?
    cases h : m.scan a with
    | found => rfl
    | absent => simp [contains, h] at hma

/-- Internal implementation detail of the hash map. -/
def getKeyD [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : α) : α :=
  (m.getKey? a).getD fallback

/-- Internal implementation detail of the hash map. -/
def getKey! [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) : α :=
  match m.getKey? a with
  | some k => k
  | none => panic! "key is not present in hash table"

end Raw₀

namespace List

/-- Compatibility predicate retained for the list-based verification layer. -/
structure HashesTo [BEq α] [Hashable α] (l : List ((a : α) × β a)) (i size : Nat) : Prop where
  /-- Every mapping in the list has the stated initial probe index. -/
  hash_self : (h : 0 < size) → ∀ p, p ∈ l → (mkIdx size h (hash p.1)).1.toNat = i

end List

/-- Compatibility predicate retained for the list-based verification layer. -/
structure IsHashSelf [BEq α] [Hashable α] (m : Array (AssocList α β)) : Prop where
  /-- Every bucket has the expected initial hash. -/
  hashes_to (i : Nat) (h : i < m.size) : List.HashesTo m[i].toList i m.size

namespace Raw

/-- The internal well-formedness predicate for linear-probing tables. -/
structure WFImp [BEq α] [Hashable α] (m : Raw α β) : Prop where
  /-- The table has at least one cell. -/
  cells_pos : 0 < m.keyArray.size
  /-- The parallel arrays have matching cells and aligned dependent values. -/
  keysValues : Raw.KeysValues m.keyArray m.valueArray
  /-- The cached size equals the number of occupied cells. -/
  size_eq : m.size = (toListModel m.buckets).length
  /-- No two stored keys compare equal. -/
  distinct : Std.Internal.List.DistinctKeys (toListModel m.buckets)
  /-- At least one cell is unused. -/
  size_lt : m.size < m.keyArray.size
  /-- Every retained key marker is reachable from the initial index of every matching query. -/
  reachable (i : Nat) (hi : i < m.keyArray.size) (k : α) (hkey : m.keyArray[i] = .some k)
      (query : α) (hmatch : k == query) :
    Raw₀.ProbePath m.keyArray m.keyArray.size (Raw₀.probeStart m.keyArray.size (hash query)) i

end Raw

end Std.DHashMap.Internal
