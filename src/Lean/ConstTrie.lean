/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Init.System.IO
public import Init.Data.Option.BasicAux
import Lean.Data.Name
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic
import Init.Data.Array.QSort
import Init.While
import Init.Omega
import Init.Data.Array.Lemmas
import Init.Data.Array.Monadic
import Init.Data.Array.Mem

namespace Lean

/-!
Prefix trees over constant names, stored per module in its olean parts and merged at import time.

Each olean part carries a prefix tree over its constant names whose nodes live in the memory-mapped
compacted region. `finalizeImport` merges the per-module trees into an `ImportedConsts` on
demand, allocating fresh nodes only for name prefixes that occur in more than one module and
sharing all single-module subtrees directly with the olean regions.
-/

/--
A prefix tree over the constant names of a single module, keyed on name components. `key` is the
full name prefix represented by a node. `children` is sorted by the (cached) hash of the child keys
and searched by binary search; as all children extend `key` by one component, comparing that final
component suffices to disambiguate equal hashes. Nodes are split by shape so that leaves and
value-less nodes store no unused fields.
-/
public inductive ConstTrie (α : Type) where
  | leaf (key : Name) (val : α)
  | inner (key : Name) (children : Array (ConstTrie α))
  | node (key : Name) (val : α) (children : Array (ConstTrie α))

public instance : Inhabited (ConstTrie α) := ⟨.inner .anonymous #[]⟩

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
@[specialize] def findChildIdx? [Inhabited β] (cs : Array β) (keyOf : β → Name) (k : Name) :
    Option Nat :=
  let h := k.hash
  scanRun h (lowerBound h 0 cs.size)
where
  /-- The first index in `[lo, hi)` whose key hash is at least `h`. -/
  @[specialize] lowerBound (h : UInt64) (lo hi : Nat) : Nat :=
    if _ : lo < hi then
      let mid := (lo + hi) / 2
      if (keyOf cs[mid]!).hash < h then lowerBound h (mid + 1) hi else lowerBound h lo mid
    else
      lo
  termination_by hi - lo
  /-- Confirms the final component among the children with key hash `h`, starting at `j`. -/
  @[specialize] scanRun (h : UInt64) (j : Nat) : Option Nat :=
    if _ : j < cs.size then
      let c := keyOf cs[j]!
      if c.hash == h then
        if lastPartEq c k then some j else scanRun h (j + 1)
      else
        none
    else
      none
  termination_by cs.size - j

/-- The name and its prefixes, innermost first, excluding the anonymous root. -/
def prefixesOf (n : Name) (acc : Array Name := .mkEmpty 8) : Array Name :=
  match n with
  | .anonymous   => acc
  | n@(.str p _) => prefixesOf p (acc.push n)
  | n@(.num p _) => prefixesOf p (acc.push n)

namespace ConstTrie

@[inline] public def key : ConstTrie α → Name
  | .leaf k _ | .inner k .. | .node k .. => k

@[inline] public def val? : ConstTrie α → Option α
  | .leaf _ v | .node _ v .. => some v
  | .inner .. => none

@[inline] public def children : ConstTrie α → Array (ConstTrie α)
  | .leaf .. => #[]
  | .inner _ cs | .node _ _ cs => cs

/-- Creates a node of the appropriate shape; `children` must be sorted by key hash. -/
public def mk (key : Name) (val? : Option α) (children : Array (ConstTrie α)) : ConstTrie α :=
  match val?, children.isEmpty with
  | some v, true => .leaf key v
  | some v, false => .node key v children
  | none, _ => .inner key children

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
def findAux (t : ConstTrie α) (path : Array Name) (i : Nat) : Option α :=
  let child (cs : Array (ConstTrie α)) (_ : i ≠ 0) : Option α :=
    match findChildIdx? cs key path[i - 1]! with
    | some j => findAux cs[j]! path (i - 1)
    | none   => none
  match t with
  | .leaf _ v => if i == 0 then some v else none
  | .inner _ cs => if h : i = 0 then none else child cs h
  | .node _ v cs => if h : i = 0 then some v else child cs h
termination_by i

public def find? (t : ConstTrie α) (n : Name) : Option α :=
  let path := prefixesOf n
  t.findAux path path.size

public def foldlM [Monad m] (t : ConstTrie α) (f : σ → Name → α → m σ) (init : σ) :
    m σ := do
  match t with
  | .leaf k v => f init k v
  | .inner _ cs => cs.foldlM (fun s c => c.foldlM f s) init
  | .node k v cs => cs.foldlM (fun s c => c.foldlM f s) (← f init k v)

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

/-- Records the edges from `cur` and its prefixes to their parents, up to the first one seen. -/
def Builder.addName (b : Builder α) (cur : Name) : Builder α :=
  if _ : cur != .anonymous && !b.seen.contains cur then
    Builder.addName { b with
      seen     := b.seen.insert cur
      children := b.children.alter (parentOf cur) fun cs? => some ((cs?.getD #[]).push cur) }
      (parentOf cur)
  else
    b
termination_by sizeOf cur
decreasing_by cases cur <;> simp_all [parentOf] <;> omega

/--
Builds the subtree for `key`. `fuel` bounds the depth of the subtree below `key`; it suffices if it
is at least the number of components of every added name.
-/
def Builder.toTrie (b : Builder α) (key : Name) : (fuel : Nat) → ConstTrie α
  | 0 => .mk key b.values[key]? #[]
  | fuel + 1 =>
    let children := b.children[key]?.getD #[] |>.map (b.toTrie · fuel)
    let children := children.qsort fun c₁ c₂ => c₁.key.hash < c₂.key.hash
    .mk key b.values[key]? children

/-- The maximal number of components of the names, sufficient fuel for `Builder.toTrie`. -/
def depthBound (names : Array Name) : Nat :=
  names.foldl (fun d n => max d n.getNumParts) 0

/-- Creates a trie mapping `names[i]` to `vals[i]`; of duplicate names, the last occurrence wins. -/
public def ofArrays (names : Array Name) (vals : Array α) : ConstTrie α :=
  (go 0 {}).toTrie .anonymous (depthBound names)
where
  go (i : Nat) (b : Builder α) : Builder α :=
    if h : i < names.size ∧ i < vals.size then
      let b : Builder α := { b with values := b.values.insert names[i] vals[i] }
      go (i + 1) (b.addName names[i])
    else
      b
  termination_by names.size - i

/-- Creates a trie containing `names` as keys. -/
public def ofNames (names : Array Name) : ConstTrie Unit := Id.run do
  let mut b : Builder Unit := {}
  for n in names do
    b := { b with values := b.values.insert n () }
    b := b.addName n
  return b.toTrie .anonymous (depthBound names)

end ConstTrie

opaque LookupCacheImpl : NonemptyType.{0}

/--
A lock-free cache for lookups in one `ImportedConsts`, implemented in C++
(`src/library/const_cache.cpp`) and freed together with it.
-/
public def LookupCache : Type := LookupCacheImpl.type

public instance : Nonempty LookupCache := by exact LookupCacheImpl.property

@[extern "lean_imported_consts_cache_new"]
public opaque LookupCache.new : BaseIO LookupCache

-- `Thunk` fields have no `sizeOf` theorems
set_option genSizeOfSpec false in
/--
Merged per-module constant prefix trees of all imported modules. Node keys and lookup work like in
`ConstTrie`; subtrees whose prefix occurs in only a single module are borrowed directly from that
module's (usually region-resident) tree.
-/
public inductive ImportedTree (α : Type) where
  /-- A subtree containing entries of only a single module: the module's own tree. -/
  | mod (modIdx : Nat) (tree : ConstTrie α)
  /--
  A node whose prefix occurs in several modules, allocated at import time. `entry?` holds the value
  together with the index of the first module declaring it.
  -/
  | merged (key : Name) (entry? : Option (α × Nat)) (children : Array (ImportedTree α))
  /--
  Like `merged`, but with the children computed on first access from the candidate subtrees
  sharing the prefix, one level at a time (see `ImportedConsts.mergeModuleTreesLazy`).
  -/
  | lazy (key : Name) (entry? : Option (α × Nat)) (children : Thunk (Array (ImportedTree α)))

public instance : Inhabited (ImportedTree α) := ⟨.merged .anonymous none #[]⟩

/--
The merged constants of all imported modules, owning the cache used by `findConstEntryCached?`
and `findExtraEntryCached?` (see `withCache`). Lookups in an `ImportedConsts` without a cache
are cached in a process-global table instead, which keeps it alive.
-/
public structure ImportedConsts (α : Type) where
  cache? : Option LookupCache := none
  tree  : ImportedTree α

public instance : Inhabited (ImportedConsts α) := ⟨{ tree := default }⟩

namespace ImportedTree

def key : ImportedTree α → Name
  | .mod _ t     => t.key
  | .merged k .. => k
  | .lazy k ..   => k

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
def findValAux : ImportedTree α → Array Name → Nat → Option α
  | .mod _ tr, path, i => tr.findAux path i
  | .lazy _ e? children, path, i =>
    if _ : i = 0 then
      e?.map (·.1)
    else
      let cs := children.get
      match findChildIdx? cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none
  | .merged _ e? cs, path, i =>
    if _ : i = 0 then
      e?.map (·.1)
    else
      match findChildIdx? cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none
termination_by _ _ i => i
decreasing_by all_goals omega

def findEntryAux : ImportedTree α → Array Name → Nat → Option (α × Nat)
  | .mod modIdx tr, path, i =>
    (tr.findAux path i).map (·, modIdx)
  | .lazy _ e? children, path, i =>
    if _ : i = 0 then
      e?
    else
      let cs := children.get
      match findChildIdx? cs key path[i - 1]! with
      | some j => findEntryAux cs[j]! path (i - 1)
      | none   => none
  | .merged _ e? cs, path, i =>
    if _ : i = 0 then
      e?
    else
      match findChildIdx? cs key path[i - 1]! with
      | some j => findEntryAux cs[j]! path (i - 1)
      | none   => none
termination_by _ _ i => i
decreasing_by all_goals omega

end ImportedTree

namespace ImportedConsts

public def empty : ImportedConsts α := { tree := .merged .anonymous none #[] }

/--
Gives `t` a fresh lookup cache, freed together with the result. The cache is an external object, so
the result cannot be compacted, e.g. into an incremental snapshot.
-/
public def withCache (t : ImportedConsts α) : BaseIO (ImportedConsts α) := do
  return { t with cache? := some (← LookupCache.new) }

/-- Finds the value for `n` together with the index of the first module declaring it. -/
public def findEntry? (t : ImportedConsts α) (n : Name) : Option (α × Nat) :=
  let path := prefixesOf n
  t.tree.findEntryAux path path.size

@[export lean_imported_extra_consts_find_entry_core]
def findExtraEntryCore (t : ImportedConsts Unit) (n : Name) : Option (Unit × Nat) :=
  t.findEntry? n

/--
Implementation of `findExtraEntryCached?` in C++ (`src/library/const_cache.cpp`), where cache hits
can avoid reference counting on `t` and the key.
-/
@[extern "lean_imported_extra_consts_find_entry_cached"]
opaque findExtraEntryCachedImpl (cache? : @& Option LookupCache)
    (t : @& ImportedConsts Unit) (n : @& Name) : Option (Unit × Nat)

/--
`findEntry?` for `importedExtraConsts`, memoized in a lock-free cache: the one owned by `t`, or
else a process-global one; sound because `t` is immutable per import set.
-/
@[inline] public def findExtraEntryCached? (t : ImportedConsts Unit) (n : Name) :
    Option (Unit × Nat) :=
  findExtraEntryCachedImpl t.cache? t n

/--
The module index of `findExtraEntryCached?` plus one, or zero if not found; returning a scalar avoids
reference counting on hits.
-/
@[extern "lean_imported_extra_consts_find_mod_idx_cached"]
opaque findExtraModIdxCachedImpl (cache? : @& Option LookupCache) (t : @& ImportedConsts Unit)
    (n : @& Name) : Nat

@[inherit_doc findExtraEntryCached?, inline]
public def findExtraModIdxCached? (t : ImportedConsts Unit) (n : Name) : Option Nat :=
  match findExtraModIdxCachedImpl t.cache? t n with
  | 0 => none
  | i + 1 => some i

public def find? (t : ImportedConsts α) (n : Name) : Option α :=
  let path := prefixesOf n
  t.tree.findValAux path path.size

/-- A constant name declared by more than one module; see `collectDuplicates`. -/
public structure Duplicate (α : Type) where
  name : Name
  /-- The declared values with their module indices, in module order. -/
  entries : Array (α × Nat)

theorem sizeOf_lt_of_mem_children {t c : ConstTrie α} (h : c ∈ t.children) :
    sizeOf c < sizeOf t := by
  cases t with
  | leaf => simp [ConstTrie.children] at h
  | inner k cs =>
    simp only [ConstTrie.children] at h; have := Array.sizeOf_lt_of_mem h; simp; omega
  | node k v cs =>
    simp only [ConstTrie.children] at h; have := Array.sizeOf_lt_of_mem h; simp; omega

/--
`c` is a child of one of the candidate nodes. `foldChildGroups` passes this fact to `multi` (as
erased proofs) for the termination of `collectDupsAux`.
-/
abbrev IsCandChild (cands : Array (Nat × ConstTrie α)) (c : ConstTrie α) : Prop :=
  ∃ p ∈ cands, c ∈ p.2.children

/-- The invariant of the child groups built by `foldChildGroups`. -/
def GroupsOk (cands : Array (Nat × ConstTrie α)) (groups : Array (Array (Nat × ConstTrie α))) :
    Prop :=
  ∀ g ∈ groups, 0 < g.size ∧ ∀ x ∈ g, IsCandChild cands x.2

theorem GroupsOk.modify {cands : Array (Nat × ConstTrie α)}
    {groups : Array (Array (Nat × ConstTrie α))} (h : GroupsOk cands groups) (gi : Nat)
    (x : Nat × ConstTrie α) (hx : IsCandChild cands x.2) :
    GroupsOk cands (groups.modify gi (·.push x)) := by
  intro g hg
  rw [Array.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  simp only [Array.size_modify] at hk
  rw [Array.getElem_modify]
  have := h groups[k] (Array.getElem_mem hk)
  split
  · simp only [Array.size_push, Array.mem_push]
    exact ⟨by omega, fun y hy => hy.elim (this.2 y) (fun e => e ▸ hx)⟩
  · exact this

theorem GroupsOk.push {cands : Array (Nat × ConstTrie α)}
    {groups : Array (Array (Nat × ConstTrie α))} (h : GroupsOk cands groups)
    (x : Nat × ConstTrie α) (hx : IsCandChild cands x.2) :
    GroupsOk cands (groups.push #[x]) := by
  intro g hg
  simp only [Array.mem_push] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · simp only [List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add,
      Nat.lt_add_one, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq, hx, and_self]

/--
Folds over the children of `cands`, the nodes of several modules for one name prefix, grouped by
key in key hash order. `single` receives a child whose key occurs in only one of the modules,
`multi` the children sharing a key, with their module indices in module order.
-/
@[inline] def foldChildGroups (cands : Array (Nat × ConstTrie α)) (init : σ)
    (single : σ → Nat → ConstTrie α → σ)
    (multi : σ → (g : Array (Nat × ConstTrie α)) → 0 < g.size →
      (∀ x ∈ g, IsCandChild cands x.2) → σ) : σ := Id.run do
  -- Flatten the candidates' children with their key hashes so that sort comparisons stay within
  -- the flattened elements, then sort by (hash, module order).
  let mut total := 0
  for (_, t) in cands do
    total := total + t.children.size
  let mut all : Array (UInt64 × Nat × {c // IsCandChild cands c}) := .mkEmpty total
  for h : p in cands do
    for h' : c in p.2.children do
      all := all.push (c.key.hash, p.1, ⟨c, p, h, h'⟩)
  let sorted := all.qsort fun (h₁, i₁, _) (h₂, i₂, _) => h₁ < h₂ || (h₁ == h₂ && i₁ < i₂)
  return go sorted 0 init
where
  @[specialize] go (sorted : Array (UInt64 × Nat × {c // IsCandChild cands c})) (idx : Nat)
      (s : σ) : σ :=
    if h : idx < sorted.size then
      let (hash₀, i, c) := sorted[idx]
      let idx := idx + 1
      if h' : idx < sorted.size then
        if sorted[idx].1 == hash₀ then
          let ⟨(groups, idx'), hgroups, _⟩ := gather sorted hash₀ idx #[#[(i, c.1)]]
            (GroupsOk.push (groups := #[]) (by simp [GroupsOk]) (i, c.1) c.2)
          go sorted idx' (flush groups hgroups 0 s)
        else
          go sorted idx (single s i c.1)
      else
        go sorted idx (single s i c.1)
    else
      s
  termination_by sorted.size - idx
  /--
  Gathers the run of children with key hash `hash₀` from `idx` on into `groups`, partitioned by
  actual key in case of hash collisions.
  -/
  gather (sorted : Array (UInt64 × Nat × {c // IsCandChild cands c})) (hash₀ : UInt64) (idx : Nat)
      (groups : Array (Array (Nat × ConstTrie α))) (hgroups : GroupsOk cands groups) :
      {r : Array (Array (Nat × ConstTrie α)) × Nat // GroupsOk cands r.1 ∧ idx ≤ r.2} :=
    if h : idx < sorted.size then
      if sorted[idx].1 == hash₀ then
        let (_, i, c) := sorted[idx]
        let ⟨groups, hgroups⟩ : {gs // GroupsOk cands gs} :=
          match groups.findIdx? fun g => lastPartEq g[0]!.2.key c.1.key with
          | some gi => ⟨groups.modify gi (·.push (i, c.1)), hgroups.modify gi (i, c.1) c.2⟩
          | none    => ⟨groups.push #[(i, c.1)], hgroups.push (i, c.1) c.2⟩
        let ⟨r, hr, hidx⟩ := gather sorted hash₀ (idx + 1) groups hgroups
        ⟨r, hr, by omega⟩
      else
        ⟨(groups, idx), hgroups, Nat.le_refl _⟩
    else
      ⟨(groups, idx), hgroups, Nat.le_refl _⟩
  termination_by sorted.size - idx
  @[specialize] flush (groups : Array (Array (Nat × ConstTrie α)))
      (hgroups : GroupsOk cands groups) (k : Nat) (s : σ) : σ :=
    if h : k < groups.size then
      let g := groups[k]
      have hg := hgroups g (Array.getElem_mem h)
      flush groups hgroups (k + 1)
        (if g.size == 1 then single s g[0]!.1 g[0]!.2 else multi s g hg.1 hg.2)
    else
      s
  termination_by groups.size - k

/-- Termination measure of `collectDupsAux`: the maximal size of a candidate node. -/
noncomputable def maxSize (cands : Array (Nat × ConstTrie α)) : Nat :=
  cands.toList.foldr (fun p m => max (sizeOf p.2) m) 0

theorem le_maxSize {cands : Array (Nat × ConstTrie α)} (h : p ∈ cands) :
    sizeOf p.2 ≤ maxSize cands := by
  rcases cands with ⟨l⟩
  simp only [maxSize, List.mem_toArray] at *
  induction l with
  | nil => simp at h
  | cons q l ih =>
    simp only [List.mem_cons, List.foldr_cons] at *
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem maxSize_lt {g cands : Array (Nat × ConstTrie α)} (hne : 0 < g.size)
    (h : ∀ x ∈ g, IsCandChild cands x.2) : maxSize g < maxSize cands := by
  have hb : ∀ x ∈ g, sizeOf x.2 < maxSize cands := fun x hx => by
    obtain ⟨p, hp, hc⟩ := h x hx
    have := sizeOf_lt_of_mem_children hc
    have := le_maxSize hp
    omega
  have hpos : 0 < maxSize cands := by
    have := hb g[0] (Array.getElem_mem hne); omega
  rcases g with ⟨l⟩
  simp only [maxSize, List.mem_toArray] at *
  clear hne h
  induction l with
  | nil => simpa using hpos
  | cons q l ih =>
    simp only [List.mem_cons, List.foldr_cons, forall_eq_or_imp] at *
    have := ih hb.2; have := hb.1; omega

def collectDupsAux (covered : Array UInt64) (key : Name)
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
    (fun acc g _ _ => collectDupsAux covered g[0]!.2.key g acc)
termination_by maxSize cands
decreasing_by exact maxSize_lt ‹_› ‹_›

/--
Collects the names declared by more than one of the given modules, with their declarations in module
order, without building an `ImportedConsts`: only name prefixes occurring in several modules are
walked. `covered` optionally gives each module a bitmask of covering direct imports; subtrees whose
modules share a mask bit are skipped, as their pairs are conflict-checked already (see
`checkImportConflicts`).
-/
public def collectDuplicates (trees : Array (Nat × ConstTrie α))
    (covered : Array UInt64 := #[]) : Array (Duplicate α) :=
  if trees.size < 2 then #[]
  else collectDupsAux covered .anonymous trees #[]

def mergeLazy (resolve : Array (α × Nat) → Option (α × Nat)) (key : Name)
    (cands : Array (Nat × ConstTrie α)) : ImportedTree α :=
  if cands.size == 1 then
    let (i, t) := cands[0]!
    .mod i t
  else
    let entries := cands.filterMap fun (i, t) => t.val?.map ((·, i))
    .lazy key (if entries.size < 2 then entries[0]? else resolve entries)
      (Thunk.mk fun _ => expandLazy cands)
termination_by (maxSize cands, 1)
decreasing_by exact Prod.Lex.right _ (by decide)
where
  expandLazy (cands : Array (Nat × ConstTrie α)) : Array (ImportedTree α) :=
    -- single-module children are borrowed as they are
    foldChildGroups cands #[] (fun cs i c => cs.push (.mod i c))
      (fun cs g _ _ => cs.push (mergeLazy resolve g[0]!.2.key g))
  termination_by (maxSize cands, 0)
  decreasing_by exact Prod.Lex.left _ _ (maxSize_lt ‹_› ‹_›)

/--
Merges per-module trees, given in module order, into a single tree, merging each node's entry and
children on first access. Only name prefixes occurring in more than one module get fresh nodes;
single-module subtrees are shared with the given trees. `resolve` picks the entry stored for a name
declared by several modules from the candidate entries, given in module order. Conflicting
declarations must have been ruled out beforehand, e.g. using `collectDuplicates`.
-/
public def mergeModuleTreesLazy (trees : Array (Nat × ConstTrie α))
    (resolve : Array (α × Nat) → Option (α × Nat) := (·[0]?)) : ImportedConsts α :=
  { tree := mergeLazy resolve .anonymous trees }

end ImportedConsts

namespace ImportedTree

/-- Replaces the node for `n` using `f`; see `ImportedConsts.modifyAt`. -/
partial def modifyAt (t : ImportedTree α) (n : Name) (f : ImportedTree α → ImportedTree α) :
    ImportedTree α :=
  match n with
  | .anonymous   => f t
  | n@(.str p _) => t.modifyAt p (modifyChild n f)
  | n@(.num p _) => t.modifyAt p (modifyChild n f)
where
  @[inline] modifyChild (n : Name) (f : ImportedTree α → ImportedTree α) :
      ImportedTree α → ImportedTree α
    | t@(.mod ..)       => t
    | .lazy k e? cs =>
      -- force the node so the modification is not lost on re-expansion
      modifyChild n f (.merged k e? cs.get)
    | .merged k e? cs =>
      match findChildIdx? cs key n with
      | some i => .merged k e? (cs.modify i f)
      | none   => .merged k e? cs

partial def foldlM [Monad m] (t : ImportedTree α) (f : σ → Name → α → m σ) (init : σ) : m σ := do
  match t with
  | .mod _ tr => tr.foldlM f init
  | .merged k e? cs =>
    let mut s := init
    if let some (v, _) := e? then
      s ← f s k v
    cs.foldlM (fun s c => c.foldlM f s) s
  | .lazy k e? children =>
    let mut s := init
    if let some (v, _) := e? then
      s ← f s k v
    children.get.foldlM (fun s c => c.foldlM f s) s

partial def foldlEntriesM [Monad m] (t : ImportedTree α) (f : σ → Name → α × Nat → m σ)
    (init : σ) : m σ := do
  match t with
  | .mod modIdx tr => tr.foldlM (fun s n v => f s n (v, modIdx)) init
  | .merged k e? cs =>
    let mut s := init
    if let some e := e? then
      s ← f s k e
    cs.foldlM (fun s c => c.foldlEntriesM f s) s
  | .lazy k e? children =>
    let mut s := init
    if let some e := e? then
      s ← f s k e
    children.get.foldlM (fun s c => c.foldlEntriesM f s) s

end ImportedTree

namespace ImportedConsts

/--
Replaces the node for `n` using `f`. `n` must be a prefix shared by several modules, such as a
`Duplicate` name; single-module subtrees are never modified. The result has no cache of its own.
-/
public def modifyAt (t : ImportedConsts α) (n : Name) (f : ImportedTree α → ImportedTree α) :
    ImportedConsts α :=
  { tree := t.tree.modifyAt n f }

public def foldlM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) : m σ :=
  t.tree.foldlM f init

public def foldl (t : ImportedConsts α) (f : σ → Name → α → σ) (init : σ) : σ :=
  t.foldlM (m := Id) f init

/-- Like `foldlM`, but also passing the index of the first module declaring each name. -/
public def foldlEntriesM [Monad m] (t : ImportedConsts α) (f : σ → Name → α × Nat → m σ)
    (init : σ) : m σ :=
  t.tree.foldlEntriesM f init

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

public def toArray (t : ImportedConsts α) : Array (Name × α) :=
  t.foldl (fun l n v => l.push (n, v)) #[]

public def values (t : ImportedConsts α) : List α :=
  t.foldl (fun l _ v => v :: l) []

public instance [Inhabited α] : GetElem? (ImportedConsts α) Name α (fun _ _ => True) where
  getElem? t n := t.find? n
  getElem t n _ := (t.find? n).get!

public instance [Monad m] : ForM m (ImportedConsts α) (Name × α) where
  forM t f := t.forM fun n v => f (n, v)

public instance [Monad m] : ForIn m (ImportedConsts α) (Name × α) := ⟨ForM.forIn⟩

end ImportedConsts

end Lean
