/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Declaration
public import Lean.Data.PersistentHashMap
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Init.Data.Array.QSort
import Init.While

namespace Lean

/-!
Prefix trees over constant names, stored per module in its olean parts and merged at import time.

Each olean part carries a prefix tree over its constant names whose nodes live in the memory-mapped
compacted region. `finalizeImport` merges the per-module trees into an `ImportedConsts` view on
demand, allocating fresh nodes only for name prefixes that occur in more than one module and
sharing all single-module subtrees directly with the olean regions.
-/

/--
A prefix tree over the constant names of a single module, keyed on name components. As all children
of a node extend its `key` by one component, comparing that final component suffices to
disambiguate equal hashes.
-/
public structure ConstTrie (α : Type) where
  /-- The full name prefix represented by the node. -/
  key : Name
  val? : Option α
  /-- Sorted by the (cached) hash of the child keys. -/
  children : Array (ConstTrie α)
  /-- Accelerates hash lookups into `children`; see the child-index layout note. -/
  childIndex : ByteArray

public instance : Inhabited (ConstTrie α) := ⟨⟨.anonymous, none, #[], .empty⟩⟩

/--
Checks whether the final components of two names agree, assuming their prefixes are already known
to be equal.
-/
@[inline] def lastPartEq : Name → Name → Bool
  | .str _ s₁, .str _ s₂ => s₁ == s₂
  | .num _ n₁, .num _ n₂ => n₁ == n₂
  | .anonymous, .anonymous => true
  | _, _ => false

/-!
A trie node's `childIndex` field has the layout
`[header : 1 byte][2^k + 1 offsets : u16 or u32 LE each][one fingerprint byte per child, in child order]`
where the header's low 5 bits hold `k` and its top bit is set iff offsets are `u32`, which is only
the case for nodes with at least `2^16 - 1` children, such as the merged root of a large import.
The children are sorted by key hash; offset `s` is the first child index whose key hash's top `k`
bits are at least `s`, so the query hash's top `k` bits select a window of on average at most one
child (`2^k ≥ #children`). Window candidates are filtered by a fingerprint byte (a further hash
byte) and confirmed by comparing the final name component, which is sound on its own: siblings
always differ in their final component. A lookup thus costs O(1) contiguous byte reads per level,
works inside memory-mapped compacted regions, and adds no per-entry heap objects.
-/

/-- Upper bound on the number of slot bits `k`, keeping the slot bits clear of `fingerprint`. -/
def maxSlotBits : UInt64 := 24

@[inline] def getU16 (bs : ByteArray) (o : Nat) : Nat :=
  ((bs.get! o).toUInt32 ||| ((bs.get! (o + 1)).toUInt32 <<< 8)).toNat

@[inline] def getU32 (bs : ByteArray) (o : Nat) : Nat :=
  ((bs.get! o).toUInt32 ||| ((bs.get! (o + 1)).toUInt32 <<< 8) |||
    ((bs.get! (o + 2)).toUInt32 <<< 16) ||| ((bs.get! (o + 3)).toUInt32 <<< 24)).toNat

/-- The top `bits` bits of `h`, for `1 ≤ bits ≤ maxSlotBits`. -/
@[inline] def topBits (h : UInt64) (bits : UInt64) : Nat :=
  (h >>> (64 - bits)).toNat

/-- The fingerprint byte of a key hash: a byte below the (up to `maxSlotBits`) slot bits. -/
@[inline] def fingerprint (h : UInt64) : UInt8 :=
  (h >>> 32).toUInt8

def pushU16 (bs : ByteArray) (v : Nat) : ByteArray :=
  let v := v.toUInt32
  (bs.push v.toUInt8).push (v >>> 8).toUInt8

def pushU32 (bs : ByteArray) (v : Nat) : ByteArray :=
  let v := v.toUInt32
  (((bs.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8

/-- Builds the child index for `cs` (sorted by key hash); see the layout note above. -/
@[specialize] def buildChildIndex [Inhabited β] (cs : Array β) (keyOf : β → Name) : ByteArray := Id.run do
  let n := cs.size
  if n == 0 then
    return .empty
  -- offsets range over `0..n`
  let wide := n ≥ 0xFFFF
  let mut bits : UInt64 := 1
  while ((1 : UInt64) <<< bits).toNat < n && bits < maxSlotBits do
    bits := bits + 1
  let slots := ((1 : UInt64) <<< bits).toNat + 1
  let width := if wide then 4 else 2
  let mut bs := ByteArray.emptyWithCapacity (1 + width * slots + n)
  bs := bs.push (if wide then bits.toUInt8 ||| 0x80 else bits.toUInt8)
  let mut j := 0
  let mut s := 0
  while s < slots do
    while j < n && topBits (keyOf cs[j]!).hash bits < s do
      j := j + 1
    bs := if wide then pushU32 bs j else pushU16 bs j
    s := s + 1
  for c in cs do
    bs := bs.push (fingerprint (keyOf c).hash)
  return bs

/--
Finds the index of the element of `cs` with key `k`, where `index` is the child index built by
`buildChildIndex` and all keys are `k`'s prefix extended by one component. Elements are only
dereferenced to confirm the final component.
-/
@[specialize] partial def findHashIdx? [Inhabited β] (index : ByteArray) (cs : Array β)
    (keyOf : β → Name) (k : Name) : Option Nat :=
  if index.size == 0 then
    none
  else
    let h := k.hash
    let header := index.get! 0
    let bits := (header &&& 0x1F).toUInt64
    let slot := topBits h bits
    if header &&& 0x80 == 0 then
      let lo := getU16 index (1 + 2 * slot)
      let hi := getU16 index (3 + 2 * slot)
      let fpOff := (3 + 2 * ((1 : UInt64) <<< bits)).toNat
      scanWindow (fingerprint h) fpOff lo hi
    else
      let lo := getU32 index (1 + 4 * slot)
      let hi := getU32 index (5 + 4 * slot)
      let fpOff := (5 + 4 * ((1 : UInt64) <<< bits)).toNat
      scanWindow (fingerprint h) fpOff lo hi
where
  @[specialize] scanWindow (fp : UInt8) (fpOff j hi : Nat) : Option Nat :=
    if j < hi then
      if index.get! (fpOff + j) == fp && lastPartEq (keyOf cs[j]!) k then
        some j
      else
        scanWindow fp fpOff (j + 1) hi
    else
      none

/-- The name and its prefixes, innermost first, excluding the anonymous root. -/
def prefixesOf (n : Name) (acc : Array Name := .mkEmpty 8) : Array Name :=
  match n with
  | .anonymous   => acc
  | n@(.str p _) => prefixesOf p (acc.push n)
  | n@(.num p _) => prefixesOf p (acc.push n)

namespace ConstTrie

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
partial def findAux (t : ConstTrie α) (path : Array Name) (i : Nat) : Option α :=
  if i == 0 then
    t.val?
  else
    match findHashIdx? t.childIndex t.children key path[i - 1]! with
    | some j => findAux t.children[j]! path (i - 1)
    | none   => none

public def find? (t : ConstTrie α) (n : Name) : Option α :=
  let path := prefixesOf n
  t.findAux path path.size

public partial def foldlM [Monad m] (t : ConstTrie α) (f : σ → Name → α → m σ) (init : σ) :
    m σ := do
  let mut s := init
  if let some v := t.val? then
    s ← f s t.key v
  t.children.foldlM (fun s c => c.foldlM f s) s

/-- Intermediate state for constructing a `ConstTrie`, mapping each prefix to its data. -/
structure Builder (α : Type) where
  values   : Std.HashMap Name α := {}
  /-- Prefixes for which the edge from their parent has been recorded already. -/
  seen     : Std.HashSet Name := {}
  children : Std.HashMap Name (Array Name) := {}

def parentOf : Name → Name
  | .anonymous => .anonymous
  | .str p _   => p
  | .num p _   => p

def Builder.addName (b : Builder α) (n : Name) : Builder α := Id.run do
  let mut b := b
  let mut cur := n
  while cur != .anonymous && !b.seen.contains cur do
    b := { b with
      seen     := b.seen.insert cur
      children := b.children.alter (parentOf cur) fun cs? => some ((cs?.getD #[]).push cur) }
    cur := parentOf cur
  return b

partial def Builder.toTrie (b : Builder α) (key : Name) : ConstTrie α :=
  let children := b.children[key]?.getD #[] |>.map (b.toTrie ·)
  let children := children.qsort fun c₁ c₂ => c₁.key.hash < c₂.key.hash
  ⟨key, b.values[key]?, children, buildChildIndex children ConstTrie.key⟩

/-- Creates a trie mapping `names[i]` to `vals[i]`. -/
public def ofArrays (names : Array Name) (vals : Array α) : ConstTrie α := Id.run do
  let mut b : Builder α := {}
  for n in names, v in vals do
    b := { b with values := b.values.insert n v }
    b := b.addName n
  return b.toTrie .anonymous

/-- Creates a trie containing `names` as keys. -/
public def ofNames (names : Array Name) : ConstTrie Unit := Id.run do
  let mut b : Builder Unit := {}
  for n in names do
    b := { b with values := b.values.insert n () }
    b := b.addName n
  return b.toTrie .anonymous

end ConstTrie

opaque LookupCacheImpl : NonemptyType.{0}

/--
A lock-free cache for lookups in one imported view, implemented in C++
(`src/library/const_cache.cpp`) and freed together with the view.
-/
public def LookupCache : Type := LookupCacheImpl.type

public instance : Nonempty LookupCache := by exact LookupCacheImpl.property

@[extern "lean_imported_consts_cache_new"]
public opaque LookupCache.new : BaseIO LookupCache

/-- The number of `LookupCache`s not yet freed, for diagnostics. -/
@[extern "lean_imported_consts_cache_num_live"]
public opaque LookupCache.numLive : BaseIO Nat

-- `Thunk` fields have no `sizeOf` theorems
set_option genSizeOfSpec false in
/--
Merged view of the per-module constant prefix trees of all imported modules. Node keys and lookup
work like in `ConstTrie`; subtrees whose prefix occurs in only a single module are borrowed
directly from that module's (usually region-resident) tree.
-/
public inductive ImportedConsts (α : Type) where
  /-- A subtree containing entries of only a single module: the module's own tree. -/
  | mod (modIdx : Nat) (tree : ConstTrie α)
  /--
  A node whose prefix occurs in several modules, allocated at import time. `entry?` holds the value
  together with the index of the first module declaring it.
  -/
  | merged (key : Name) (entry? : Option (α × Nat)) (children : Array (ImportedConsts α))
      (childIndex : ByteArray)
  /--
  Like `merged`, but with the entry and children computed on first access from the candidate
  subtrees sharing the prefix, one level at a time; the entry resolution rule is fixed at merge
  time (see `mergeModuleTreesLazy`). Thunk forcing is thread-safe and supported on persistent
  objects, so lazy nodes are safe to share across elaboration threads.
  -/
  | lazy (key : Name) (entry : Thunk (Option (α × Nat)))
      (expanded : Thunk (Array (ImportedConsts α) × ByteArray))
  /--
  The root of a view, owning the cache used by `findConstEntryCached?` and `findExtraEntryCached?`;
  see `withCache`. Views without a cache, including ones whose cache was emptied by `dropCache`,
  are cached in a process-global table instead, which keeps them alive. The C++ cache identifies
  this constructor by its index, so it must stay the fourth one.
  -/
  | cached (cache : Option LookupCache) (tree : ImportedConsts α)

public instance : Inhabited (ImportedConsts α) := ⟨.merged .anonymous none #[] .empty⟩

namespace ImportedConsts

public def empty : ImportedConsts α := .merged .anonymous none #[] .empty

def key : ImportedConsts α → Name
  | .mod _ t     => t.key
  | .merged k .. => k
  | .lazy k ..   => k
  | .cached _ t  => t.key

/-- Creates a `merged` node, computing the child index; `children` must be sorted by key hash. -/
public def mkMerged (key : Name) (entry? : Option (α × Nat))
    (children : Array (ImportedConsts α)) : ImportedConsts α :=
  .merged key entry? children (buildChildIndex children ImportedConsts.key)

/-- Wraps `t` in a `cached` root with a fresh lookup cache, freed together with the result. -/
public def withCache (t : ImportedConsts α) : BaseIO (ImportedConsts α) := do
  return .cached (some (← LookupCache.new)) t

/--
Empties the cache field of a `cached` root in place, so that the view can be compacted; lookups
then use the process-global cache. The emptied cache is leaked, as concurrent lookups may still use
it.
-/
@[extern "lean_imported_consts_drop_cache"]
public opaque dropCache (t : @& ImportedConsts α) : BaseIO Unit

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
partial def findValAux : ImportedConsts α → Array Name → Nat → Option α
  | .mod _ tr, path, i => tr.findAux path i
  | .lazy _ entry expanded, path, i =>
    if i == 0 then
      entry.get.map (·.1)
    else
      let (cs, hs) := expanded.get
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none
  | .cached _ t, path, i => findValAux t path i
  | .merged _ e? cs hs, path, i =>
    if i == 0 then
      match e? with
      | some (v, _) => some v
      | none        => none
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none

partial def findModIdxAux : ImportedConsts α → Array Name → Nat → Option Nat
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some _ => some modIdx
    | none   => none
  | .lazy _ entry expanded, path, i =>
    if i == 0 then
      entry.get.map (·.2)
    else
      let (cs, hs) := expanded.get
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findModIdxAux cs[j]! path (i - 1)
      | none   => none
  | .cached _ t, path, i => findModIdxAux t path i
  | .merged _ e? cs hs, path, i =>
    if i == 0 then
      match e? with
      | some (_, modIdx) => some modIdx
      | none             => none
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findModIdxAux cs[j]! path (i - 1)
      | none   => none

partial def findEntryAux : ImportedConsts α → Array Name → Nat → Option (α × Nat)
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some v => some (v, modIdx)
    | none   => none
  | .lazy _ entry expanded, path, i =>
    if i == 0 then
      entry.get
    else
      let (cs, hs) := expanded.get
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findEntryAux cs[j]! path (i - 1)
      | none   => none
  | .cached _ t, path, i => findEntryAux t path i
  | .merged _ e? cs hs, path, i =>
    if i == 0 then
      e?
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findEntryAux cs[j]! path (i - 1)
      | none   => none

/-- Finds the value for `n` together with the index of the first module declaring it. -/
public def findEntry? (t : ImportedConsts α) (n : Name) : Option (α × Nat) :=
  let path := prefixesOf n
  t.findEntryAux path path.size

@[export lean_imported_consts_find_entry_core]
def findEntryCore (t : ImportedConsts ConstantInfo) (n : Name) :
    Option (ConstantInfo × Nat) :=
  t.findEntry? n

/--
`findEntry?` for the constants view, memoized in a lock-free cache: the one owned by a `cached`
root, or else a process-global one; sound because the imported view is immutable per import set.
Implemented in C++ (`src/library/const_cache.cpp`) where cache hits can avoid reference counting
on the view and key.
-/
@[extern "lean_imported_consts_find_entry_cached"]
public opaque findConstEntryCached? (t : @& ImportedConsts ConstantInfo) (n : @& Name) :
    Option (ConstantInfo × Nat)

@[inherit_doc findConstEntryCached?, inline]
public def findConstCached? (t : ImportedConsts ConstantInfo) (n : Name) : Option ConstantInfo :=
  match t.findConstEntryCached? n with
  | some (c, _) => some c
  | none        => none

@[inherit_doc findConstEntryCached?, inline]
public def findConstModIdxCached? (t : ImportedConsts ConstantInfo) (n : Name) : Option Nat :=
  match t.findConstEntryCached? n with
  | some (_, modIdx) => some modIdx
  | none             => none

@[export lean_imported_extra_consts_find_entry_core]
def findExtraEntryCore (t : ImportedConsts Unit) (n : Name) : Option (Unit × Nat) :=
  t.findEntry? n

@[inherit_doc findConstEntryCached?, extern "lean_imported_extra_consts_find_entry_cached"]
public opaque findExtraEntryCached? (t : @& ImportedConsts Unit) (n : @& Name) :
    Option (Unit × Nat)

@[inherit_doc findConstEntryCached?, inline]
public def findExtraModIdxCached? (t : ImportedConsts Unit) (n : Name) : Option Nat :=
  match t.findExtraEntryCached? n with
  | some (_, modIdx) => some modIdx
  | none             => none

/--
Empties the process-global lookup cache used for views without a `cached` root, e.g. after
persisting the environment when the cache contents are not expected to be useful anymore. Entries are leaked, as concurrent readers may still
hold them; clearing merely reopens their slots.
-/
@[extern "lean_imported_consts_cache_reset"]
public opaque resetCache : IO Unit

public def find? (t : ImportedConsts α) (n : Name) : Option α :=
  let path := prefixesOf n
  t.findValAux path path.size

public def findModIdx? (t : ImportedConsts α) (n : Name) : Option Nat :=
  let path := prefixesOf n
  t.findModIdxAux path path.size

public def contains (t : ImportedConsts α) (n : Name) : Bool :=
  t.find? n |>.isSome

/-- A constant name declared by more than one module; see `collectDuplicates`. -/
public structure Duplicate (α : Type) where
  name : Name
  /-- The declared values with their module indices, in module order. -/
  entries : Array (α × Nat)

/--
Folds over the children of `cands`, the nodes of several modules for one name prefix, grouped by
key in key hash order. `single` receives a child whose key occurs in only one of the modules,
`multi` the children sharing a key, with their module indices in module order.
-/
@[inline] def foldChildGroups (cands : Array (Nat × ConstTrie α)) (init : σ)
    (single : σ → Nat → ConstTrie α → σ) (multi : σ → Array (Nat × ConstTrie α) → σ) : σ :=
    Id.run do
  -- Flatten the candidates' children with their key hashes so that sort comparisons stay within
  -- the flattened elements, then sort by (hash, module order).
  let mut total := 0
  for (_, t) in cands do
    total := total + t.children.size
  let mut all : Array (UInt64 × Nat × ConstTrie α) := .mkEmpty total
  for (i, t) in cands do
    for c in t.children do
      all := all.push (c.key.hash, i, c)
  let sorted := all.qsort fun (h₁, i₁, _) (h₂, i₂, _) => h₁ < h₂ || (h₁ == h₂ && i₁ < i₂)
  let mut s := init
  let mut idx := 0
  while idx < sorted.size do
    let (hash₀, i, c) := sorted[idx]!
    idx := idx + 1
    if idx == sorted.size || sorted[idx]!.1 != hash₀ then
      s := single s i c
    else
      -- gather the run of children with the same key hash, partitioned by actual key in case of
      -- hash collisions
      let mut groups : Array (Array (Nat × ConstTrie α)) := #[#[(i, c)]]
      while idx < sorted.size && sorted[idx]!.1 == hash₀ do
        let (_, i, c) := sorted[idx]!
        match groups.findIdx? fun g => lastPartEq g[0]!.2.key c.key with
        | some gi => groups := groups.modify gi (·.push (i, c))
        | none    => groups := groups.push #[(i, c)]
        idx := idx + 1
      for g in groups do
        s := if g.size == 1 then single s g[0]!.1 g[0]!.2 else multi s g
  return s

partial def collectDupsAux (covered : Array UInt64) (key : Name)
    (cands : Array (Nat × ConstTrie α)) (acc : Array (Duplicate α)) : Array (Duplicate α) :=
    Id.run do
  -- Modules jointly covered by one direct import (a common mask bit) are pairwise
  -- conflict-checked already; nothing below this prefix needs visiting.
  unless covered.isEmpty do
    let mut common : UInt64 := 0xFFFFFFFFFFFFFFFF
    for (i, _) in cands do
      common := common &&& covered[i]!
    if common != 0 then
      return acc
  let mut acc := acc
  let entries := cands.filterMap fun (i, t) => t.val?.map ((·, i))
  if entries.size > 1 then
    acc := acc.push { name := key, entries }
  -- no duplicate can hide below a single-module subtree, so those are skipped without a visit
  return foldChildGroups cands acc (fun acc _ _ => acc)
    (fun acc g => collectDupsAux covered g[0]!.2.key g acc)

/--
Collects the names declared by more than one of the given modules, with their declarations in
module order, without building a merged view: only name prefixes occurring in several modules are
walked. `covered` optionally gives each module a bitmask of covering direct imports; subtrees
whose modules share a mask bit are skipped, as their pairs are conflict-checked already (see
`checkImportConflicts`).
-/
public def collectDuplicates (trees : Array (Nat × ConstTrie α))
    (covered : Array UInt64 := #[]) : Array (Duplicate α) :=
  if trees.size < 2 then #[]
  else collectDupsAux covered .anonymous trees #[]

partial def mergeLazy (resolve : Array (α × Nat) → Option (α × Nat)) (key : Name)
    (cands : Array (Nat × ConstTrie α)) : ImportedConsts α :=
  if cands.size == 1 then
    let (i, t) := cands[0]!
    .mod i t
  else
    .lazy key
      (Thunk.mk fun _ => resolve <| cands.filterMap fun (i, t) => t.val?.map ((·, i)))
      (Thunk.mk fun _ => expandLazy cands)
where
  expandLazy (cands : Array (Nat × ConstTrie α)) : Array (ImportedConsts α) × ByteArray :=
    -- single-module children are borrowed as they are
    let children := foldChildGroups cands #[] (fun cs i c => cs.push (.mod i c))
      (fun cs g => cs.push (mergeLazy resolve g[0]!.2.key g))
    (children, buildChildIndex children ImportedConsts.key)

/--
Merges per-module trees, given in module order, into a single view, merging each node's entry and
children on first access. Only name prefixes occurring in more than one module get fresh nodes;
single-module subtrees are shared with the given trees. `resolve` picks the entry stored for a name
declared by several modules from the candidate entries, given in module order. Conflicting
declarations must have been ruled out beforehand, e.g. using `collectDuplicates`.
-/
public def mergeModuleTreesLazy (trees : Array (Nat × ConstTrie α))
    (resolve : Array (α × Nat) → Option (α × Nat) := (·[0]?)) : ImportedConsts α :=
  mergeLazy resolve .anonymous trees

/--
Replaces the node for `n` using `f`. `n` must be a prefix shared by several modules, such as a
`Duplicate` name; single-module subtrees are never modified.
-/
public partial def modifyAt (t : ImportedConsts α) (n : Name)
    (f : ImportedConsts α → ImportedConsts α) : ImportedConsts α :=
  match n with
  | .anonymous   => f t
  | n@(.str p _) => t.modifyAt p (modifyChild n f)
  | n@(.num p _) => t.modifyAt p (modifyChild n f)
where
  @[inline] modifyChild (n : Name) (f : ImportedConsts α → ImportedConsts α) :
      ImportedConsts α → ImportedConsts α
    | t@(.mod ..)       => t
    | .cached _ t       => modifyChild n f t
    | .lazy k e exp =>
      -- force the node so the modification is not lost on re-expansion
      let (cs, hs) := exp.get
      modifyChild n f (.merged k e.get cs hs)
    | .merged k e? cs hs =>
      match findHashIdx? hs cs key n with
      | some i => .merged k e? (cs.modify i f) hs
      | none   => .merged k e? cs hs

/--
Recursively forces all lazily merged nodes into `merged` nodes. Compacting an environment, such
as for `--incr-header-save`, forces the thunks anyway; doing so eagerly instead avoids running
merges in the middle of compaction and compacting the thunk wrappers themselves.
-/
public partial def forceExpanded : ImportedConsts α → ImportedConsts α
  | .lazy k entry expanded =>
    let (cs, hs) := expanded.get
    .merged k entry.get (cs.map forceExpanded) hs
  | .merged k e? cs hs => .merged k e? (cs.map forceExpanded) hs
  -- caches cannot be compacted
  | .cached _ t        => forceExpanded t
  | t                  => t

public partial def foldlM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) :
    m σ := do
  match t with
  | .mod _ tr => tr.foldlM f init
  | .merged k e? cs _ =>
    let mut s := init
    if let some (v, _) := e? then
      s ← f s k v
    cs.foldlM (fun s c => c.foldlM f s) s
  | .lazy k entry expanded =>
    let mut s := init
    if let some (v, _) := entry.get then
      s ← f s k v
    (expanded.get).1.foldlM (fun s c => c.foldlM f s) s
  | .cached _ t => t.foldlM f init

public def foldl (t : ImportedConsts α) (f : σ → Name → α → σ) (init : σ) : σ :=
  t.foldlM (m := Id) f init

/-- Like `foldlM`, but also passing the index of the first module declaring each name. -/
public partial def foldlEntriesM [Monad m] (t : ImportedConsts α)
    (f : σ → Name → α × Nat → m σ) (init : σ) : m σ := do
  match t with
  | .mod modIdx tr => tr.foldlM (fun s n v => f s n (v, modIdx)) init
  | .merged k e? cs _ =>
    let mut s := init
    if let some e := e? then
      s ← f s k e
    cs.foldlM (fun s c => c.foldlEntriesM f s) s
  | .lazy k entry expanded =>
    let mut s := init
    if let some e := entry.get then
      s ← f s k e
    (expanded.get).1.foldlM (fun s c => c.foldlEntriesM f s) s
  | .cached _ t => t.foldlEntriesM f init

public def forM [Monad m] (t : ImportedConsts α) (f : Name → α → m PUnit) : m PUnit :=
  t.foldlM (fun _ n v => f n v) ⟨⟩

public def size (t : ImportedConsts α) : Nat :=
  t.foldl (fun n _ _ => n + 1) 0

@[inherit_doc foldlM]
public def fold (t : ImportedConsts α) (f : σ → Name → α → σ) (init : σ) : σ :=
  t.foldl f init

@[inherit_doc foldlM]
public def foldM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) : m σ :=
  t.foldlM f init

public def toList (t : ImportedConsts α) : List (Name × α) :=
  t.foldl (fun l n v => (n, v) :: l) []

public def toArray (t : ImportedConsts α) : Array (Name × α) :=
  t.foldl (fun l n v => l.push (n, v)) #[]

public def keys (t : ImportedConsts α) : List Name :=
  t.foldl (fun l n _ => n :: l) []

public def values (t : ImportedConsts α) : List α :=
  t.foldl (fun l _ v => v :: l) []

public instance [Inhabited α] : GetElem? (ImportedConsts α) Name α (fun _ _ => True) where
  getElem? t n := t.find? n
  getElem t n _ := (t.find? n).get!

public instance [Monad m] : ForM m (ImportedConsts α) (Name × α) where
  forM t f := t.forM fun n v => f (n, v)

public instance [Monad m] : ForIn m (ImportedConsts α) (Name × α) := ⟨ForM.forIn⟩

end ImportedConsts

/--
The constants of an environment: the imported constants merged from the per-olean prefix trees
plus the constants declared in the current module.
-/
public structure ConstMap where
  /-- Constants from imported modules. -/
  map₁ : ImportedConsts ConstantInfo := .empty
  /-- Constants declared in the current module. -/
  map₂ : PHashMap Name ConstantInfo := {}

public instance : Inhabited ConstMap := ⟨{}⟩

namespace ConstMap

public def find? (m : ConstMap) (n : Name) : Option ConstantInfo :=
  match m.map₂.find? n with
  | r@(some _) => r
  | none       => m.map₁.findConstCached? n

/--
Similar to `find?`, but searches the imported constants first. So, the result is correct only if
imported constants are never overwritten.
-/
public def find?' (m : ConstMap) (n : Name) : Option ConstantInfo :=
  match m.map₁.findConstCached? n with
  | r@(some _) => r
  | none       => m.map₂.find? n

public def contains (m : ConstMap) (n : Name) : Bool :=
  m.map₂.contains n || (m.map₁.findConstCached? n).isSome

public def insert (m : ConstMap) (n : Name) (v : ConstantInfo) : ConstMap :=
  { m with map₂ := m.map₂.insert n v }

/-- Folds over the constants declared in the current module. -/
@[inline] public def foldStage2 (f : σ → Name → ConstantInfo → σ) (s : σ) (m : ConstMap) : σ :=
  m.map₂.foldl f s

public def foldM {m : Type → Type} [Monad m] (f : σ → Name → ConstantInfo → m σ) (init : σ)
    (map : ConstMap) : m σ := do
  map.map₂.foldlM f (← map.map₁.foldlM f init)

public def fold (f : σ → Name → ConstantInfo → σ) (init : σ) (m : ConstMap) : σ :=
  m.map₂.foldl f (m.map₁.foldl f init)

public def forM {m : Type → Type} [Monad m] (map : ConstMap) (f : Name → ConstantInfo → m PUnit) :
    m PUnit := do
  map.map₁.forM f
  map.map₂.forM f

public instance {m : Type → Type} [Monad m] : ForM m ConstMap (Name × ConstantInfo) where
  forM map f := map.forM fun n v => f (n, v)

public instance {m : Type → Type} [Monad m] : ForIn m ConstMap (Name × ConstantInfo) :=
  ⟨ForM.forIn⟩

public def toList (m : ConstMap) : List (Name × ConstantInfo) :=
  m.fold (init := []) fun es n v => (n, v) :: es

end ConstMap

end Lean
