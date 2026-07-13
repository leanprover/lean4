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

Instead of eagerly inserting every imported constant into one big hash map, each olean part carries
a prefix tree over its constant names whose nodes live in the memory-mapped compacted region.
`finalizeImport` merges the per-module trees into an `ImportedConsts` view, allocating fresh nodes
only for name prefixes that occur in more than one module and sharing all single-module subtrees
directly with the olean regions.
-/

/--
A prefix tree over the constant names of a single module, keyed on name components. `key` is the
full name prefix represented by the node. `children` is sorted by the (cached) hash of the child
keys and `childIndex` accelerates hash lookups into it (see the child-index layout note); as all
children extend `key` by one component, comparing that final component suffices to disambiguate
equal hashes.
-/
public inductive ConstTrie (α : Type) where
  | node (key : Name) (val? : Option α) (children : Array (ConstTrie α))
      (childIndex : ByteArray)

public instance : Inhabited (ConstTrie α) := ⟨.node .anonymous none #[] .empty⟩

/--
Checks whether the final components of two names agree, assuming their prefixes are already known
to be equal.
-/
@[inline] private def lastPartEq : Name → Name → Bool
  | .str _ s₁, .str _ s₂ => s₁ == s₂
  | .num _ n₁, .num _ n₂ => n₁ == n₂
  | .anonymous, .anonymous => true
  | _, _ => false

/-!
A trie node's `childIndex` field has the layout
`[k : 1 byte][2^k + 1 offsets : u16 LE each][one fingerprint byte per child, in child order]`.
The children are sorted by key hash; offset `s` is the first child index whose key hash's top `k`
bits are at least `s`, so the query hash's top `k` bits select a window of on average at most one
child (`2^k ≥ #children`). Window candidates are filtered by a fingerprint byte (a further hash
byte) and confirmed by comparing the final name component, which is sound on its own: siblings
always differ in their final component. A lookup thus costs O(1) contiguous byte reads per level,
works inside memory-mapped compacted regions, and adds no per-entry heap objects.
-/

@[inline] private def getU16 (bs : ByteArray) (o : Nat) : Nat :=
  ((bs.get! o).toUInt32 ||| ((bs.get! (o + 1)).toUInt32 <<< 8)).toNat

@[inline] private def topBits (h : UInt64) (bits : UInt64) : Nat :=
  ((h >>> 48) >>> (16 - bits)).toNat

/-- The fingerprint byte of a key hash: the byte below the (up to 16) slot bits. -/
@[inline] private def fingerprint (h : UInt64) : UInt8 :=
  (h >>> 40).toUInt8

private def pushU16 (bs : ByteArray) (v : Nat) : ByteArray :=
  let v := v.toUInt32
  (bs.push v.toUInt8).push (v >>> 8).toUInt8

/-- Builds the child index for `cs` (sorted by key hash); see the layout note above. -/
@[specialize] private def buildChildIndex [Inhabited β] (cs : Array β) (keyOf : β → Name) : ByteArray := Id.run do
  let n := cs.size
  if n == 0 then
    return .empty
  -- `u16` offsets bound the node width; trie nodes are nowhere near this wide
  assert! n < 0xFFFF
  let mut bits : UInt64 := 1
  while ((1 : UInt64) <<< bits).toNat < n && bits < 16 do
    bits := bits + 1
  let slots := ((1 : UInt64) <<< bits).toNat + 1
  let mut bs := ByteArray.emptyWithCapacity (1 + 2 * slots + n)
  bs := bs.push bits.toUInt8
  let mut j := 0
  let mut s := 0
  while s < slots do
    while j < n && topBits (keyOf cs[j]!).hash bits < s do
      j := j + 1
    bs := pushU16 bs j
    s := s + 1
  for c in cs do
    bs := bs.push (fingerprint (keyOf c).hash)
  return bs

/--
Finds the index of the element of `cs` with key `k`, where `index` is the child index built by
`buildChildIndex` and all keys are `k`'s prefix extended by one component. Elements are only
dereferenced to confirm the final component.
-/
@[specialize] private partial def findHashIdx? [Inhabited β] (index : ByteArray) (cs : Array β)
    (keyOf : β → Name) (k : Name) : Option Nat :=
  if index.size == 0 then
    none
  else
    let h := k.hash
    let bits := (index.get! 0).toUInt64
    let slot := topBits h bits
    let lo := getU16 index (1 + 2 * slot)
    let hi := getU16 index (3 + 2 * slot)
    let fpOff := (3 + 2 * ((1 : UInt64) <<< bits)).toNat
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
private def prefixesOf (n : Name) (acc : Array Name := .mkEmpty 8) : Array Name :=
  match n with
  | .anonymous   => acc
  | n@(.str p _) => prefixesOf p (acc.push n)
  | n@(.num p _) => prefixesOf p (acc.push n)

namespace ConstTrie

public def key : ConstTrie α → Name
  | .node k .. => k

public def val? : ConstTrie α → Option α
  | .node _ v .. => v

public def children : ConstTrie α → Array (ConstTrie α)
  | .node _ _ cs _ => cs

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
partial def findAux (t : ConstTrie α) (path : Array Name) (i : Nat) : Option α :=
  match t with
  | .node _ v? cs hs =>
    if i == 0 then
      v?
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findAux cs[j]! path (i - 1)
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
private structure Builder (α : Type) where
  values   : Std.HashMap Name α := {}
  /-- Prefixes for which the edge from their parent has been recorded already. -/
  seen     : Std.HashSet Name := {}
  children : Std.HashMap Name (Array Name) := {}

private def parentOf : Name → Name
  | .anonymous => .anonymous
  | .str p _   => p
  | .num p _   => p

private def Builder.addName (b : Builder α) (n : Name) : Builder α := Id.run do
  let mut b := b
  let mut cur := n
  while cur != .anonymous && !b.seen.contains cur do
    b := { b with
      seen     := b.seen.insert cur
      children := b.children.alter (parentOf cur) fun cs? => some ((cs?.getD #[]).push cur) }
    cur := parentOf cur
  return b

private partial def Builder.toTrie (b : Builder α) (key : Name) : ConstTrie α :=
  let children := b.children[key]?.getD #[] |>.map (b.toTrie ·)
  let children := children.qsort fun c₁ c₂ => c₁.key.hash < c₂.key.hash
  .node key b.values[key]? children (buildChildIndex children ConstTrie.key)

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

public instance : Inhabited (ImportedConsts α) := ⟨.merged .anonymous none #[] .empty⟩

namespace ImportedConsts

public def empty : ImportedConsts α := .merged .anonymous none #[] .empty

def key : ImportedConsts α → Name
  | .mod _ t     => t.key
  | .merged k .. => k

/-- Creates a `merged` node, computing the child index; `children` must be sorted by key hash. -/
public def mkMerged (key : Name) (entry? : Option (α × Nat))
    (children : Array (ImportedConsts α)) : ImportedConsts α :=
  .merged key entry? children (buildChildIndex children ImportedConsts.key)

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
private partial def findValAux : ImportedConsts α → Array Name → Nat → Option α
  | .mod _ tr, path, i => tr.findAux path i
  | .merged _ e? cs hs, path, i =>
    if i == 0 then
      match e? with
      | some (v, _) => some v
      | none        => none
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none

private partial def findModIdxAux : ImportedConsts α → Array Name → Nat → Option Nat
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some _ => some modIdx
    | none   => none
  | .merged _ e? cs hs, path, i =>
    if i == 0 then
      match e? with
      | some (_, modIdx) => some modIdx
      | none             => none
    else
      match findHashIdx? hs cs key path[i - 1]! with
      | some j => findModIdxAux cs[j]! path (i - 1)
      | none   => none

private partial def findEntryAux : ImportedConsts α → Array Name → Nat → Option (α × Nat)
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some v => some (v, modIdx)
    | none   => none
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
private def findEntryCore (t : ImportedConsts ConstantInfo) (n : Name) :
    Option (ConstantInfo × Nat) :=
  t.findEntry? n

/--
`findEntry?` for the constants view, memoized in a process-global, lock-free cache; sound because
the imported view is immutable per import set. Implemented in C++ (`src/library/const_cache.cpp`)
where cache hits can avoid reference counting on the view and key.
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
private def findExtraEntryCore (t : ImportedConsts Unit) (n : Name) : Option (Unit × Nat) :=
  t.findEntry? n

@[inherit_doc findConstEntryCached?, extern "lean_imported_extra_consts_find_entry_cached"]
public opaque findExtraEntryCached? (t : @& ImportedConsts Unit) (n : @& Name) :
    Option (Unit × Nat)

@[inherit_doc findConstEntryCached?, inline]
public def findExtraModIdxCached? (t : ImportedConsts Unit) (n : Name) : Option Nat :=
  match t.findExtraEntryCached? n with
  | some (_, modIdx) => some modIdx
  | none             => none

public def find? (t : ImportedConsts α) (n : Name) : Option α :=
  let path := prefixesOf n
  t.findValAux path path.size

public def findModIdx? (t : ImportedConsts α) (n : Name) : Option Nat :=
  let path := prefixesOf n
  t.findModIdxAux path path.size

public def contains (t : ImportedConsts α) (n : Name) : Bool :=
  t.find? n |>.isSome

/-- A constant name declared by more than one module; see `mergeModuleTrees`. -/
public structure Duplicate (α : Type) where
  name : Name
  /-- The declared values with their module indices, in module order. -/
  entries : Array (α × Nat)

private partial def mergeCands (key : Name) (cands : Array (Nat × ConstTrie α)) :
    StateM (Array (Duplicate α)) (ImportedConsts α) := do
  if cands.size == 1 then
    let (i, t) := cands[0]!
    return .mod i t
  let entries := cands.filterMap fun (i, t) => t.val?.map ((·, i))
  if entries.size > 1 then
    modify (·.push { name := key, entries })
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
  let mut children := #[]
  let mut idx := 0
  while idx < sorted.size do
    let (hash₀, i, c) := sorted[idx]!
    idx := idx + 1
    if idx == sorted.size || sorted[idx]!.1 != hash₀ then
      -- sole child with this key hash, so from a single module: borrow the subtree
      children := children.push (.mod i c)
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
        children := children.push (← mergeCands g[0]!.2.key g)
  return .merged key entries[0]? children (buildChildIndex children ImportedConsts.key)

/--
Merges per-module trees, given in module order, into a single view. Only name prefixes occurring in
more than one module get fresh nodes; single-module subtrees are shared with the given trees.
Names declared by more than one module are additionally reported as `Duplicate`s, with the first
declaration stored in the tree; use `setEntry` to overwrite it if a later declaration is preferred.
-/
public def mergeModuleTrees (trees : Array (Nat × ConstTrie α)) :
    ImportedConsts α × Array (Duplicate α) :=
  mergeCands .anonymous trees |>.run #[]

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
    | .merged k e? cs hs =>
      match findHashIdx? hs cs key n with
      | some i => .merged k e? (cs.modify i f) hs
      | none   => .merged k e? cs hs

/-- Overwrites the entry for `n`, which must be a `Duplicate`-reported name. -/
public def setEntry (t : ImportedConsts α) (n : Name) (e : α × Nat) : ImportedConsts α :=
  t.modifyAt n fun
    | .merged k _ cs hs => .merged k (some e) cs hs
    | t                 => t

public partial def foldlM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) :
    m σ := do
  match t with
  | .mod _ tr => tr.foldlM f init
  | .merged k e? cs _ =>
    let mut s := init
    if let some (v, _) := e? then
      s ← f s k v
    cs.foldlM (fun s c => c.foldlM f s) s

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
