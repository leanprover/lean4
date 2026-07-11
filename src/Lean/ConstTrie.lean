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
keys for binary search; as all children extend `key` by one component, comparing that final
component suffices to disambiguate equal hashes.
-/
public inductive ConstTrie (α : Type) where
  | node (key : Name) (val? : Option α) (children : Array (ConstTrie α))

public instance : Inhabited (ConstTrie α) := ⟨.node .anonymous none #[]⟩

/--
Checks whether the final components of two names agree, assuming their prefixes are already known
to be equal.
-/
@[inline] private def lastPartEq : Name → Name → Bool
  | .str _ s₁, .str _ s₂ => s₁ == s₂
  | .num _ n₁, .num _ n₂ => n₁ == n₂
  | .anonymous, .anonymous => true
  | _, _ => false

/--
Scans the run of elements with key hash `h` starting at `i` for the key matching `k`'s final
component.
-/
@[specialize] private partial def scanEqualRun [Inhabited β] (cs : Array β) (keyOf : β → Name)
    (k : Name) (h : UInt64) (i : Nat) : Option Nat :=
  if i < cs.size then
    let ck := keyOf cs[i]!
    if ck.hash != h then
      none
    else if lastPartEq ck k then
      some i
    else
      scanEqualRun cs keyOf k h (i + 1)
  else
    none

/--
Finds the index of the element of `cs` with key `k`, where `cs` is sorted by key hash and all keys
are `k`'s prefix extended by one component.
-/
@[specialize] private partial def findSortedIdx? [Inhabited β] (cs : Array β) (keyOf : β → Name)
    (k : Name) : Option Nat :=
  lowerBound k.hash 0 cs.size
where
  @[specialize] lowerBound (h : UInt64) (lo hi : Nat) : Option Nat :=
    if lo < hi then
      let mid := (lo + hi) / 2
      if (keyOf cs[mid]!).hash < h then
        lowerBound h (mid + 1) hi
      else
        lowerBound h lo mid
    else
      scanEqualRun cs keyOf k h lo

/-- The name and its prefixes, innermost first, excluding the anonymous root. -/
private def prefixesOf (n : Name) (acc : Array Name := .mkEmpty 8) : Array Name :=
  match n with
  | .anonymous   => acc
  | n@(.str p _) => prefixesOf p (acc.push n)
  | n@(.num p _) => prefixesOf p (acc.push n)

namespace ConstTrie

public def key : ConstTrie α → Name
  | .node k _ _ => k

public def val? : ConstTrie α → Option α
  | .node _ v _ => v

public def children : ConstTrie α → Array (ConstTrie α)
  | .node _ _ cs => cs

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
partial def findAux (t : ConstTrie α) (path : Array Name) (i : Nat) : Option α :=
  if i == 0 then
    t.val?
  else
    match findSortedIdx? t.children key path[i - 1]! with
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
  .node key b.values[key]? <| children.qsort fun c₁ c₂ => c₁.key.hash < c₂.key.hash

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
  /--
  A `merged` node with many children, augmented by a map from child key hash to the first child
  index with that hash; see `indexWide`. Only ever wraps a `merged` node.
  -/
  | indexed (index : Std.HashMap UInt64 Nat) (node : ImportedConsts α)

public instance : Inhabited (ImportedConsts α) := ⟨.merged .anonymous none #[]⟩

namespace ImportedConsts

public def empty : ImportedConsts α := .merged .anonymous none #[]

def key : ImportedConsts α → Name
  | .mod _ t      => t.key
  | .merged k ..  => k
  | .indexed _ t  => t.key

/-- Walks from `t`, the node for `path[i]` (or the root for `i = path.size`), to `path[0]`. -/
private partial def findValAux : ImportedConsts α → Array Name → Nat → Option α
  | .mod _ tr, path, i => tr.findAux path i
  | .merged _ e? cs, path, i =>
    if i == 0 then
      match e? with
      | some (v, _) => some v
      | none        => none
    else
      match findSortedIdx? cs key path[i - 1]! with
      | some j => findValAux cs[j]! path (i - 1)
      | none   => none
  | .indexed index t@(.merged _ _ cs), path, i =>
    if i == 0 then
      findValAux t path i
    else
      let k := path[i - 1]!
      match index[k.hash]? with
      | some j =>
        match scanEqualRun cs key k k.hash j with
        | some j => findValAux cs[j]! path (i - 1)
        | none   => none
      | none => none
  | .indexed _ t, path, i => findValAux t path i

private partial def findModIdxAux : ImportedConsts α → Array Name → Nat → Option Nat
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some _ => some modIdx
    | none   => none
  | .merged _ e? cs, path, i =>
    if i == 0 then
      match e? with
      | some (_, modIdx) => some modIdx
      | none             => none
    else
      match findSortedIdx? cs key path[i - 1]! with
      | some j => findModIdxAux cs[j]! path (i - 1)
      | none   => none
  | .indexed index t@(.merged _ _ cs), path, i =>
    if i == 0 then
      findModIdxAux t path i
    else
      let k := path[i - 1]!
      match index[k.hash]? with
      | some j =>
        match scanEqualRun cs key k k.hash j with
        | some j => findModIdxAux cs[j]! path (i - 1)
        | none   => none
      | none => none
  | .indexed _ t, path, i => findModIdxAux t path i

private partial def findEntryAux : ImportedConsts α → Array Name → Nat → Option (α × Nat)
  | .mod modIdx tr, path, i =>
    match tr.findAux path i with
    | some v => some (v, modIdx)
    | none   => none
  | .merged _ e? cs, path, i =>
    if i == 0 then
      e?
    else
      match findSortedIdx? cs key path[i - 1]! with
      | some j => findEntryAux cs[j]! path (i - 1)
      | none   => none
  | .indexed index t@(.merged _ _ cs), path, i =>
    if i == 0 then
      findEntryAux t path i
    else
      let k := path[i - 1]!
      match index[k.hash]? with
      | some j =>
        match scanEqualRun cs key k k.hash j with
        | some j => findEntryAux cs[j]! path (i - 1)
        | none   => none
      | none => none
  | .indexed _ t, path, i => findEntryAux t path i

/-- Finds the value for `n` together with the index of the first module declaring it. -/
public def findEntry? (t : ImportedConsts α) (n : Name) : Option (α × Nat) :=
  let path := prefixesOf n
  t.findEntryAux path path.size

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
  let all := cands.flatMap fun (i, t) => t.children.map ((i, ·))
  let all := all.qsort fun (i₁, c₁) (i₂, c₂) =>
    c₁.key.hash < c₂.key.hash || (c₁.key.hash == c₂.key.hash && i₁ < i₂)
  let mut children := #[]
  let mut idx := 0
  while idx < all.size do
    -- gather the run of children with the same key hash, partitioned by actual key in case of
    -- hash collisions
    let hash₀ := all[idx]!.2.key.hash
    let mut groups : Array (Array (Nat × ConstTrie α)) := #[]
    while idx < all.size && all[idx]!.2.key.hash == hash₀ do
      let (i, c) := all[idx]!
      match groups.findIdx? fun g => lastPartEq g[0]!.2.key c.key with
      | some gi => groups := groups.modify gi (·.push (i, c))
      | none    => groups := groups.push #[(i, c)]
      idx := idx + 1
    for g in groups do
      children := children.push (← mergeCands g[0]!.2.key g)
  return .merged key entries[0]? children

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
    | t@(.mod ..)      => t
    | .indexed index t => .indexed index (modifyChild n f t)
    | .merged k e? cs  =>
      match findSortedIdx? cs key n with
      | some i => .merged k e? (cs.modify i f)
      | none   => .merged k e? cs

/-- Overwrites the entry for `n`, which must be a `Duplicate`-reported name. -/
public def setEntry (t : ImportedConsts α) (n : Name) (e : α × Nat) : ImportedConsts α :=
  t.modifyAt n fun
    | .merged k _ cs => .merged k (some e) cs
    | t              => t

/--
Wraps merged nodes that have at least `threshold` children in an `indexed` node mapping each child
key hash to the first child index with that hash, turning the per-level binary search into a single
probe on the widest nodes. Apply only after all `setEntry` fixups; `setEntry` does not descend into
`indexed` nodes.
-/
public partial def indexWide (t : ImportedConsts α) (threshold : Nat := 16) : ImportedConsts α :=
  match t with
  | .mod ..     => t
  | .indexed .. => t
  | .merged k e? cs =>
    let cs := cs.map (indexWide · threshold)
    let node : ImportedConsts α := .merged k e? cs
    if cs.size < threshold then
      node
    else
      .indexed (buildIndex cs 0 (.emptyWithCapacity cs.size)) node
where
  buildIndex (cs : Array (ImportedConsts α)) (j : Nat) (index : Std.HashMap UInt64 Nat) :
      Std.HashMap UInt64 Nat :=
    if h : j < cs.size then
      buildIndex cs (j + 1) (index.insertIfNew cs[j].key.hash j)
    else
      index

public partial def foldlM [Monad m] (t : ImportedConsts α) (f : σ → Name → α → m σ) (init : σ) :
    m σ := do
  match t with
  | .mod _ tr => tr.foldlM f init
  | .indexed _ t => t.foldlM f init
  | .merged k e? cs =>
    let mut s := init
    if let some (v, _) := e? then
      s ← f s k v
    cs.foldlM (fun s c => c.foldlM f s) s

public def foldl (t : ImportedConsts α) (f : σ → Name → α → σ) (init : σ) : σ :=
  t.foldlM (m := Id) f init

public def forM [Monad m] (t : ImportedConsts α) (f : Name → α → m PUnit) : m PUnit :=
  t.foldlM (fun _ n v => f n v) ⟨⟩

public def size (t : ImportedConsts α) : Nat :=
  t.foldl (fun n _ _ => n + 1) 0

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
  imported : ImportedConsts ConstantInfo := .empty
  /-- Constants declared in the current module. -/
  locals   : PHashMap Name ConstantInfo := {}

public instance : Inhabited ConstMap := ⟨{}⟩

namespace ConstMap

public def find? (m : ConstMap) (n : Name) : Option ConstantInfo :=
  match m.locals.find? n with
  | r@(some _) => r
  | none       => m.imported.find? n

/--
Similar to `find?`, but searches the imported constants first. So, the result is correct only if
imported constants are never overwritten.
-/
public def find?' (m : ConstMap) (n : Name) : Option ConstantInfo :=
  match m.imported.find? n with
  | r@(some _) => r
  | none       => m.locals.find? n

public def contains (m : ConstMap) (n : Name) : Bool :=
  m.locals.contains n || m.imported.contains n

public def insert (m : ConstMap) (n : Name) (v : ConstantInfo) : ConstMap :=
  { m with locals := m.locals.insert n v }

/-- Folds over the constants declared in the current module. -/
@[inline] public def foldStage2 (f : σ → Name → ConstantInfo → σ) (s : σ) (m : ConstMap) : σ :=
  m.locals.foldl f s

public def foldM {m : Type → Type} [Monad m] (f : σ → Name → ConstantInfo → m σ) (init : σ)
    (map : ConstMap) : m σ := do
  map.locals.foldlM f (← map.imported.foldlM f init)

public def fold (f : σ → Name → ConstantInfo → σ) (init : σ) (m : ConstMap) : σ :=
  m.locals.foldl f (m.imported.foldl f init)

public def forM {m : Type → Type} [Monad m] (map : ConstMap) (f : Name → ConstantInfo → m PUnit) :
    m PUnit := do
  map.imported.forM f
  map.locals.forM f

public instance {m : Type → Type} [Monad m] : ForM m ConstMap (Name × ConstantInfo) where
  forM map f := map.forM fun n v => f (n, v)

public instance {m : Type → Type} [Monad m] : ForIn m ConstMap (Name × ConstantInfo) :=
  ⟨ForM.forIn⟩

public def toList (m : ConstMap) : List (Name × ConstantInfo) :=
  m.fold (init := []) fun es n v => (n, v) :: es

end ConstMap

end Lean
