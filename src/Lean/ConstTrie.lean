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
Per-module locators for constant names, stored in the olean parts and merged at import time.

Each olean part sorts its constant names by the prefix tree root that covers them (see `ConstTrie`)
and stores a prefix tree over just these roots, in the memory-mapped compacted region. A lookup
walks the tree to the root covering the name and binary-searches the root's range of the name
array. `finalizeImport` merges the per-module trees into an `ImportedConsts` view on demand,
allocating fresh nodes only for name prefixes that occur in more than one module.
-/

/--
A locator over the names of a single module (its constants or its extra constants), keyed on name
components. Each name is covered by a *root*: its shortest proper prefix that is a name of the
module (or, for extra constants, one of its constants), or else the name itself. Roots never extend
each other, so they are exactly the leaves of the tree; a leaf stores the range `[lo, hi)` of the
module's order (see `ModuleConsts`) that lists the names it covers, sorted by `Name.quickCmp`. `key`
is the full name prefix represented by a node, and `children` is sorted by the (cached) hash of the
child keys.
-/
public inductive ConstTrie where
  | inner (key : Name) (children : Array ConstTrie)
  | leaf (key : Name) (lo hi : UInt32)

public instance : Inhabited ConstTrie := ⟨.inner .anonymous #[]⟩

/--
Checks whether the final components of two names agree, assuming their prefixes are already known
to be equal.
-/
@[inline] def lastPartEq : Name → Name → Bool
  | .str _ s₁, .str _ s₂ => s₁ == s₂
  | .num _ n₁, .num _ n₂ => n₁ == n₂
  | .anonymous, .anonymous => true
  | _, _ => false

/--
Finds the index of the element of `cs` with key `k`, where `cs` is sorted by key hash and all keys
are `k`'s prefix extended by one component.
-/
@[specialize] partial def findChildIdx? [Inhabited β] (cs : Array β) (keyOf : β → Name) (k : Name) :
    Option Nat :=
  let h := k.hash
  scanRun h (lowerBound h 0 cs.size)
where
  /-- The first index in `[lo, hi)` whose key hash is at least `h`. -/
  @[specialize] lowerBound (h : UInt64) (lo hi : Nat) : Nat :=
    if lo < hi then
      let mid := (lo + hi) / 2
      if (keyOf cs[mid]!).hash < h then lowerBound h (mid + 1) hi else lowerBound h lo mid
    else
      lo
  /-- Confirms the final component among the children with key hash `h`, starting at `j`. -/
  @[specialize] scanRun (h : UInt64) (j : Nat) : Option Nat :=
    if j < cs.size then
      let c := keyOf cs[j]!
      if c.hash == h then
        if lastPartEq c k then some j else scanRun h (j + 1)
      else
        none
    else
      none

/-- The `k`-th entry of an order, a sequence of little-endian `UInt32` indices. -/
@[inline] def orderAt (order : ByteArray) (k : Nat) : Nat :=
  let o := 4 * k
  ((order.get! o).toUInt32 ||| ((order.get! (o + 1)).toUInt32 <<< 8) |||
    ((order.get! (o + 2)).toUInt32 <<< 16) ||| ((order.get! (o + 3)).toUInt32 <<< 24)).toNat

/-- Encodes `perm` as an order; see `orderAt`. -/
def encodeOrder (perm : Array Nat) : ByteArray := Id.run do
  let mut bs := ByteArray.emptyWithCapacity (4 * perm.size)
  for i in perm do
    let v := i.toUInt32
    bs := (((bs.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push (v >>> 24).toUInt8
  return bs

/--
The index in `names` of `n`, searching the positions `[lo, hi)` of `order`, along which `names` is
sorted by `Name.quickCmp`.
-/
partial def binSearchName (names : Array Name) (order : ByteArray) (n : Name) (lo hi : Nat) :
    Option Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    let idx := orderAt order mid
    match n.quickCmp names[idx]! with
    | .lt => binSearchName names order n lo mid
    | .gt => binSearchName names order n (mid + 1) hi
    | .eq => some idx
  else
    none

/-- The name and its prefixes, innermost first, excluding the anonymous root. -/
def prefixesOf (n : Name) (acc : Array Name := .mkEmpty 8) : Array Name :=
  match n with
  | .anonymous   => acc
  | n@(.str p _) => prefixesOf p (acc.push n)
  | n@(.num p _) => prefixesOf p (acc.push n)

namespace ConstTrie

@[inline] public def key : ConstTrie → Name
  | .inner k _ | .leaf k .. => k

@[inline] public def children : ConstTrie → Array ConstTrie
  | .inner _ cs => cs
  | .leaf .. => #[]

/--
Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), towards `path[0]` and
returns the name range of the root covering `path[0]`, if any.
-/
partial def locate (t : ConstTrie) (path : Array Name) (i : Nat) : Option (Nat × Nat) :=
  match t with
  | .leaf _ lo hi => some (lo.toNat, hi.toNat)
  | .inner _ cs =>
    if i == 0 then
      none
    else
      match findChildIdx? cs key path[i - 1]! with
      | some j => locate cs[j]! path (i - 1)
      | none   => none

def parentOf : Name → Name
  | .anonymous => .anonymous
  | .str p _   => p
  | .num p _   => p

/-- The edges between the given roots and their prefixes. -/
def childrenOf (roots : Array Name) : Std.HashMap Name (Array Name) := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut children : Std.HashMap Name (Array Name) := {}
  for r in roots do
    let mut cur := r
    while cur != .anonymous && !seen.contains cur do
      seen := seen.insert cur
      children := children.alter (parentOf cur) fun cs? => some ((cs?.getD #[]).push cur)
      cur := parentOf cur
  return children

partial def toTrie (children : Std.HashMap Name (Array Name)) (ranges : Std.HashMap Name (Nat × Nat))
    (key : Name) : ConstTrie :=
  match ranges[key]? with
  | some (lo, hi) => .leaf key lo.toUInt32 hi.toUInt32
  | none =>
    let cs := children[key]?.getD #[] |>.map (toTrie children ranges ·)
    .inner key (cs.qsort fun c₁ c₂ => c₁.key.hash < c₂.key.hash)

/--
Builds the locator for `names`, where `isOwner` holds for the names that may serve as roots (a
superset of `names`). Returns the trie and the order it indexes, listing the indices of `names`
grouped by root and sorted by `Name.quickCmp` within each root.
-/
public def build (names : Array Name) (isOwner : Name → Bool) : ConstTrie × ByteArray := Id.run do
  let roots := names.map fun n => Id.run do
    let mut root := n
    let mut cur := parentOf n
    while cur != .anonymous do
      if isOwner cur then
        root := cur
      cur := parentOf cur
    return root
  let mut rootSet : Std.HashSet Name := {}
  for r in roots do
    rootSet := rootSet.insert r
  let sortedRoots := rootSet.toArray.qsort fun a b => a.quickCmp b == .lt
  let mut rootIdx : Std.HashMap Name Nat := {}
  for h : k in [0:sortedRoots.size] do
    rootIdx := rootIdx.insert sortedRoots[k] k
  let rootIdxs := roots.map (rootIdx[·]!)
  let perm := (Array.range names.size).qsort fun a b =>
    let ra := rootIdxs[a]!
    let rb := rootIdxs[b]!
    ra < rb || (ra == rb && names[a]!.quickCmp names[b]! == .lt)
  let mut ranges : Std.HashMap Name (Nat × Nat) := {}
  let mut j := 0
  while j < perm.size do
    let r := rootIdxs[perm[j]!]!
    let lo := j
    while j < perm.size && rootIdxs[perm[j]!]! == r do
      j := j + 1
    ranges := ranges.insert sortedRoots[r]! (lo, j)
  return (toTrie (childrenOf sortedRoots) ranges .anonymous, encodeOrder perm)

end ConstTrie

/--
The names of a single module (its constants or its extra constants) together with their values and
locator; see `ConstTrie`. `order` lists the indices of `names` in the order the locator's ranges
refer to.
-/
public structure ModuleConsts (α : Type) where
  names : Array Name
  val : Nat → α
  trie : ConstTrie
  order : ByteArray

namespace ModuleConsts

/-- The position of `n` in `m.names`. -/
public def findIdx? (m : ModuleConsts α) (n : Name) : Option Nat :=
  let path := prefixesOf n
  match m.trie.locate path path.size with
  | some (lo, hi) => binSearchName m.names m.order n lo hi
  | none          => none

public def find? (m : ModuleConsts α) (n : Name) : Option α :=
  m.findIdx? n |>.map m.val

/-- Builds the module data for `names` and `vals`, taking `owners` as roots in addition to `names`. -/
public def ofArrays (names : Array Name) (vals : Array α) [Inhabited α]
    (owners : Std.HashSet Name := {}) : ModuleConsts α :=
  let owners := names.foldl (·.insert ·) owners
  let (trie, order) := ConstTrie.build names owners.contains
  { names, val := (vals[·]!), trie, order }

end ModuleConsts

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
A node of the merged locator of several modules. Subtrees whose prefix occurs in only a single
module are borrowed directly from that module's (usually region-resident) locator; nodes whose
prefix occurs in several modules record the modules whose roots end there (`owners`, as module
index and name range) and merge their children.
-/
public inductive ImportedNode where
  | mod (modIdx : Nat) (tree : ConstTrie)
  | merged (key : Name) (owners : Array (Nat × Nat × Nat)) (children : Array ImportedNode)
  /--
  Like `merged`, but with the children computed on first access from the candidate subtrees sharing
  the prefix, one level at a time. Thunk forcing is thread-safe and supported on persistent
  objects, so lazy nodes are safe to share across elaboration threads.
  -/
  | lazy (key : Name) (owners : Array (Nat × Nat × Nat)) (children : Thunk (Array ImportedNode))

public instance : Inhabited ImportedNode := ⟨.merged .anonymous #[] #[]⟩

namespace ImportedNode

def key : ImportedNode → Name
  | .mod _ t     => t.key
  | .merged k .. => k
  | .lazy k ..   => k

/-- Collects the name ranges of the roots covering `path[0]`, walking from `t`, the node for `path[i]`. -/
partial def collect (t : ImportedNode) (path : Array Name) (i : Nat) (acc : Array (Nat × Nat × Nat)) :
    Array (Nat × Nat × Nat) :=
  match t with
  | .mod modIdx tr =>
    match tr.locate path i with
    | some (lo, hi) => acc.push (modIdx, lo, hi)
    | none          => acc
  | .merged _ owners cs => go owners cs
  | .lazy _ owners cs => go owners cs.get
where
  @[inline] go (owners : Array (Nat × Nat × Nat)) (cs : Array ImportedNode) :
      Array (Nat × Nat × Nat) :=
    let acc := acc ++ owners
    if i == 0 then
      acc
    else
      match findChildIdx? cs key path[i - 1]! with
      | some j => collect cs[j]! path (i - 1) acc
      | none   => acc

/-- Recursively forces all lazily merged nodes. -/
partial def force : ImportedNode → ImportedNode
  | .lazy k owners cs => .merged k owners (cs.get.map force)
  | .merged k owners cs => .merged k owners (cs.map force)
  | t@(.mod ..) => t

end ImportedNode

/--
Folds over the children of `cands`, the nodes of several modules for one name prefix, grouped by
key in key hash order. `single` receives a child whose key occurs in only one of the modules,
`multi` the children sharing a key, with their module indices in module order.
-/
@[inline] def foldChildGroups (cands : Array (Nat × ConstTrie)) (init : σ)
    (single : σ → Nat → ConstTrie → σ) (multi : σ → Array (Nat × ConstTrie) → σ) : σ :=
    Id.run do
  -- Flatten the candidates' children with their key hashes so that sort comparisons stay within
  -- the flattened elements, then sort by (hash, module order).
  let mut total := 0
  for (_, t) in cands do
    total := total + t.children.size
  let mut all : Array (UInt64 × Nat × ConstTrie) := .mkEmpty total
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
      let mut groups : Array (Array (Nat × ConstTrie)) := #[#[(i, c)]]
      while idx < sorted.size && sorted[idx]!.1 == hash₀ do
        let (_, i, c) := sorted[idx]!
        match groups.findIdx? fun g => lastPartEq g[0]!.2.key c.key with
        | some gi => groups := groups.modify gi (·.push (i, c))
        | none    => groups := groups.push #[(i, c)]
        idx := idx + 1
      for g in groups do
        s := if g.size == 1 then single s g[0]!.1 g[0]!.2 else multi s g
  return s

partial def mergeNodes (key : Name) (cands : Array (Nat × ConstTrie)) : ImportedNode :=
  if cands.size == 1 then
    let (i, t) := cands[0]!
    .mod i t
  else
    let owners := cands.filterMap fun
      | (i, .leaf _ lo hi) => some (i, lo.toNat, hi.toNat)
      | _ => none
    .lazy key owners <| Thunk.mk fun _ =>
      -- single-module children are borrowed as they are
      foldChildGroups (cands.filter (·.2 matches .inner ..)) #[] (fun cs i c => cs.push (.mod i c))
        (fun cs g => cs.push (mergeNodes g[0]!.2.key g))

/--
Merged view of the constants (or extra constants) of all imported modules; see `ImportedNode`.
`mods` holds the module data by module index, and `resolve` picks the entry for a name declared by
several modules from the candidate entries, given in module order. The C++ lookup cache reads
`cache`, so it must stay the first field.
-/
public structure ImportedConsts (α : Type) where
  /--
  The cache used by `findConstEntryCached?` and `findExtraEntryCached?`; see `withCache`. Views
  without a cache, including ones whose cache was emptied by `dropCache`, are cached in a
  process-global table instead, which keeps them alive.
  -/
  cache : Option LookupCache := none
  mods : Array (Option (ModuleConsts α)) := #[]
  root : ImportedNode := default
  resolve : Array (α × Nat) → Option (α × Nat) := (·[0]?)
  /-- Entries replacing the ones of the modules, for testing. -/
  overrides : PersistentHashMap Name (α × Nat) := {}

public instance : Inhabited (ImportedConsts α) := ⟨{}⟩

namespace ImportedConsts

public def empty : ImportedConsts α := {}

/--
Merges the data of the given modules, given in module order with indices below `numMods`, into a
single view, merging nodes on first access. Conflicting declarations must have been ruled out
beforehand, e.g. using `collectDuplicates`.
-/
public def mergeModules (numMods : Nat) (mods : Array (Nat × ModuleConsts α))
    (resolve : Array (α × Nat) → Option (α × Nat) := (·[0]?)) : ImportedConsts α :=
  let modArr := mods.foldl (init := .replicate numMods none) fun arr (i, m) => arr.set! i (some m)
  { mods := modArr, root := mergeNodes .anonymous (mods.map fun (i, m) => (i, m.trie)), resolve }

/-- Wraps `t` in a view with a fresh lookup cache, freed together with the result. -/
public def withCache (t : ImportedConsts α) : BaseIO (ImportedConsts α) := do
  return { t with cache := some (← LookupCache.new) }

/--
Empties the cache field of `t` in place, so that the view can be compacted; lookups then use the
process-global cache. The emptied cache is leaked, as concurrent lookups may still use it.
-/
@[extern "lean_imported_consts_drop_cache"]
public opaque dropCache (t : @& ImportedConsts α) : BaseIO Unit

/-- Finds the value for `n` together with the index of the first module declaring it. -/
public def findEntry? (t : ImportedConsts α) (n : Name) : Option (α × Nat) := Id.run do
  if let some e := t.overrides.find? n then
    return some e
  let path := prefixesOf n
  let cands := t.root.collect path path.size #[]
  let mut hits : Array (α × Nat) := #[]
  for (i, lo, hi) in cands do
    if let some (some m) := t.mods[i]? then
      if let some idx := binSearchName m.names m.order n lo hi then
        hits := hits.push (m.val idx, i)
  if hits.size ≤ 1 then
    return hits[0]?
  else
    return t.resolve (hits.qsort (·.2 < ·.2))

@[export lean_imported_consts_find_entry_core]
def findEntryCore (t : ImportedConsts ConstantInfo) (n : Name) :
    Option (ConstantInfo × Nat) :=
  t.findEntry? n

/--
`findEntry?` for the constants view, memoized in a lock-free cache: the one owned by the view, or
else a process-global one; sound because the imported view is immutable per import set.
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
Empties the process-global lookup cache used for views without their own cache, e.g. after
persisting the environment when the cache contents are not expected to be useful anymore. Entries
are leaked, as concurrent readers may still hold them; clearing merely reopens their slots.
-/
@[extern "lean_imported_consts_cache_reset"]
public opaque resetCache : IO Unit

public def find? (t : ImportedConsts α) (n : Name) : Option α :=
  t.findEntry? n |>.map (·.1)

public def findModIdx? (t : ImportedConsts α) (n : Name) : Option Nat :=
  t.findEntry? n |>.map (·.2)

public def contains (t : ImportedConsts α) (n : Name) : Bool :=
  t.findEntry? n |>.isSome

/--
Replaces the entry for `n`, keeping the index of the module declaring it, for testing. The result
has no lookup cache of its own.
-/
public def override (t : ImportedConsts α) (n : Name) (v : α) : ImportedConsts α :=
  let modIdx := (t.findEntry? n).map (·.2) |>.getD 0
  { t with cache := none, overrides := t.overrides.insert n (v, modIdx) }

/--
Forces all lazily merged nodes and drops the lookup cache. Compacting an environment, such as for
`--incr-header-save`, forces the thunks anyway; doing so eagerly instead avoids running merges in
the middle of compaction and compacting the thunk wrappers themselves, and caches cannot be
compacted.
-/
public def forceExpanded (t : ImportedConsts α) : ImportedConsts α :=
  { t with cache := none, root := t.root.force }

/--
Folds over all names, passing each name's entry once, from the module it is attributed to (see
`findEntry?`). Names that only one module can declare are taken directly from the module arrays;
names that other modules' roots also cover are checked by a lookup.
-/
public partial def foldlEntriesM [Monad m] (t : ImportedConsts α) (f : σ → Name → α × Nat → m σ)
    (init : σ) : m σ :=
  goNode t.root #[] init
where
  /-- Folds over the range `[lo, hi)` of module `i`, with lookups iff `check`. -/
  goRange (i lo hi : Nat) (check : Bool) (s : σ) : m σ := do
    let some (some md) := t.mods[i]? | return s
    let mut s := s
    for k in [lo:hi] do
      let idx := orderAt md.order k
      let n := md.names[idx]!
      if check then
        if let some e := t.findEntry? n then
          if e.2 == i then
            s ← f s n e
      else
        s ← f s n (md.val idx, i)
    return s
  goTree (i : Nat) (check : Bool) (tr : ConstTrie) (s : σ) : m σ :=
    match tr with
    | .leaf _ lo hi => goRange i lo.toNat hi.toNat check s
    | .inner _ cs => cs.foldlM (fun s c => goTree i check c s) s
  /-- `ownerMods` are the modules owning a prefix above `node`. -/
  goNode (node : ImportedNode) (ownerMods : Array Nat) (s : σ) : m σ := do
    match node with
    | .mod i tr => goTree i (ownerMods.any (· != i) || !t.overrides.isEmpty) tr s
    | .merged _ owners cs => goShared owners cs ownerMods s
    | .lazy _ owners cs => goShared owners cs.get ownerMods s
  /-- At a node shared by several modules, owner ranges may overlap other modules' names. -/
  goShared (owners : Array (Nat × Nat × Nat)) (cs : Array ImportedNode) (ownerMods : Array Nat)
      (s : σ) : m σ := do
    let mut s := s
    for (i, lo, hi) in owners do
      s ← goRange i lo hi true s
    let ownerMods := ownerMods ++ owners.map (·.1)
    cs.foldlM (fun s c => goNode c ownerMods s) s

public def foldlM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) : m σ :=
  t.foldlEntriesM (fun s n (v, _) => f s n v) init

public def foldl (t : ImportedConsts α) (f : σ → Name → α → σ) (init : σ) : σ :=
  t.foldlM (m := Id) f init

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

/-- A constant name declared by more than one module; see `collectDuplicates`. -/
public structure Duplicate (α : Type) where
  name : Name
  /-- The declared values with their module indices, in module order. -/
  entries : Array (α × Nat)

/-- Accumulated duplicates: for each name, the entries found so far. -/
abbrev DupAcc (α : Type) := Std.HashMap Name (Array (α × Nat))

/--
Records the names of module `i`'s range `[lo, hi)` that also occur in one of the `owners` ranges of
other modules, skipping module pairs already covered by a common direct import.
-/
def checkRange (mods : Array (Option (ModuleConsts α))) (covered : Array UInt64)
    (owners : Array (Nat × Nat × Nat)) (i lo hi : Nat) (acc : DupAcc α) : DupAcc α := Id.run do
  let some (some mi) := mods[i]? | return acc
  let others := owners.filter fun (j, _, _) =>
    j != i && (covered.isEmpty || covered[i]! &&& covered[j]! == 0)
  if others.isEmpty then
    return acc
  let mut acc := acc
  for k in [lo:hi] do
    let idx := orderAt mi.order k
    let n := mi.names[idx]!
    for (j, lo', hi') in others do
      let some (some mj) := mods[j]? | continue
      if let some k := binSearchName mj.names mj.order n lo' hi' then
        let add (es : Array (α × Nat)) (e : α × Nat) :=
          if es.any (·.2 == e.2) then es else es.push e
        acc := acc.alter n fun es? =>
          some (add (add (es?.getD #[]) (mi.val idx, i)) (mj.val k, j))
  return acc

/-- Checks all roots of module `i`'s subtree `t` against `owners`. -/
partial def checkSubtree (mods : Array (Option (ModuleConsts α))) (covered : Array UInt64)
    (owners : Array (Nat × Nat × Nat)) (i : Nat) (t : ConstTrie) (acc : DupAcc α) : DupAcc α :=
  let owners := owners.filter fun (j, _, _) =>
    j != i && (covered.isEmpty || covered[i]! &&& covered[j]! == 0)
  if owners.isEmpty then acc else go owners t acc
where
  go (owners : Array (Nat × Nat × Nat)) : ConstTrie → DupAcc α → DupAcc α
    | .leaf _ lo hi, acc => checkRange mods covered owners i lo.toNat hi.toNat acc
    | .inner _ cs, acc => cs.foldl (fun acc c => go owners c acc) acc

partial def sweep (mods : Array (Option (ModuleConsts α))) (covered : Array UInt64)
    (cands : Array (Nat × ConstTrie)) (above : Array (Nat × Nat × Nat)) (acc : DupAcc α) :
    DupAcc α := Id.run do
  -- Modules jointly covered by one direct import (a common mask bit) are pairwise
  -- conflict-checked already; nothing below this prefix needs visiting.
  unless covered.isEmpty do
    let mut common : UInt64 := 0xFFFFFFFFFFFFFFFF
    for (i, _) in cands do
      common := common &&& covered[i]!
    for (j, _, _) in above do
      common := common &&& covered[j]!
    if common != 0 then
      return acc
  let mut acc := acc
  let mut owners := above
  for (i, t) in cands do
    if let .leaf _ lo hi := t then
      acc := checkRange mods covered owners i lo.toNat hi.toNat acc
      owners := owners.push (i, lo.toNat, hi.toNat)
  let inners := cands.filter (·.2 matches .inner ..)
  -- a single-module subtree can only hide duplicates of names owned further up
  return foldChildGroups inners acc
    (fun acc i c => if owners.isEmpty then acc else checkSubtree mods covered owners i c acc)
    (fun acc g => sweep mods covered g owners acc)

/--
Collects the names declared by more than one of the given modules, with their declarations in
module order, without building a merged view. `covered` optionally gives each module (by index) a
bitmask of covering direct imports; module pairs sharing a mask bit are skipped, as they are
conflict-checked already (see `checkImportConflicts`).
-/
public def collectDuplicates (numMods : Nat) (mods : Array (Nat × ModuleConsts α))
    (covered : Array UInt64 := #[]) : Array (Duplicate α) := Id.run do
  if mods.size < 2 then
    return #[]
  let modArr := mods.foldl (init := .replicate numMods none) fun arr (i, m) => arr.set! i (some m)
  let acc := sweep modArr covered (mods.map fun (i, m) => (i, m.trie)) #[] {}
  return acc.toArray.map fun (name, entries) => { name, entries := entries.qsort (·.2 < ·.2) }

end ImportedConsts

/--
The constants of an environment: the imported constants merged from the per-olean locators plus the
constants declared in the current module.
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
