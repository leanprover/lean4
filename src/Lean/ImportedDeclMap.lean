/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.ResolveName
import Init.Data.Array.QSort

namespace Lean

/-!
Maps keyed by declarations whose imported part is assembled from per-module data without inserting
every entry: an entry about a constant declared in the module that added it is looked up in that
module's sorted array, found using the imported constants, and only the remaining entries are kept
in a hash map.
-/

/-- Keys of an `ImportedDeclMap`: a declaration name plus possibly more data. -/
public class ImportedDeclMap.Key (κ : Type) where
  declName : κ → Name
  /-- A strict total order compatible with `==`, for binary search. -/
  lt : κ → κ → Bool

public instance : ImportedDeclMap.Key Name where
  declName := id
  lt := Name.quickLt

/-- The imported part of a `DeclMap`. -/
public structure ImportedDeclMap (κ α : Type) [BEq κ] [Hashable κ] where
  /-- The imported constants, used to find the module declaring a constant. -/
  consts  : ImportedConsts ConstantInfo := .empty
  /-- Per module index, the keys of the entries owned by the module (see `isOwned`), sorted. -/
  ownedKeys : Array (Array κ) := #[]
  /--
  Per module index, the values of the owned entries, in the order of `ownedKeys`, or no values if
  they are all `default`.
  -/
  ownedVals : Array (Array α) := #[]
  /-- The entries not owned by the module declaring their constant; they override owned entries. -/
  foreign : PHashMap κ α := {}
  /-- The number of keys. -/
  size    : Nat := 0
  deriving Inhabited

namespace ImportedDeclMap

variable {κ α : Type} [BEq κ] [Hashable κ] [Key κ] [Inhabited α]

/--
Whether the current module owns an entry about constant `n`: it declares `n`, which does not have a
reserved name. Constants with reserved names, such as equational theorems, may be realized by several
modules.
-/
public def isOwned (env : Environment) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).isNone && !isReservedName env n

/--
Sorts the entries a module owns by key, keeping the last entry of each key, and returns their keys
and values.
-/
public def sortOwned (es : Array (κ × α)) : Array κ × Array α :=
  let es := es.mapIdx fun i e => (i, e)
  let es := es.qsort fun (i₁, k₁, _) (i₂, k₂, _) => Key.lt k₁ k₂ || (k₁ == k₂ && i₁ > i₂)
  es.foldl (init := (#[], #[])) fun (ks, vs) (_, k, v) =>
    if ks.back?.any (· == k) then (ks, vs) else (ks.push k, vs.push v)

/-- The index of `k` in the sorted array `ks`. -/
def findIdx? (ks : Array κ) (k : κ) : Option Nat :=
  go 0 ks.size
where
  go (lo hi : Nat) : Option Nat :=
    if _ : lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < ks.size then
        let k' := ks[mid]
        if Key.lt k' k then go (mid + 1) hi
        else if Key.lt k k' then go lo mid
        else some mid
      else
        none
    else
      none
  termination_by hi - lo

def findOwned? (m : ImportedDeclMap κ α) (k : κ) : Option α := do
  if m.ownedKeys.isEmpty then none
  let i ← m.consts.findConstModIdxCached? (Key.declName k)
  let j ← findIdx? (m.ownedKeys[i]?.getD #[]) k
  return (m.ownedVals[i]?.getD #[])[j]?.getD default

/--
Assembles the imported entries of all modules, given in module order: those owned by a module, as
returned by `sortOwned` (possibly without values if they are all `default`), at the module's index,
and the remaining ones, of which later ones override earlier ones.
-/
public def ofModules (consts : ImportedConsts ConstantInfo) (owned : Array (Array κ × Array α))
    (foreign : Array (Array (κ × α))) : ImportedDeclMap κ α := Id.run do
  let mut m : ImportedDeclMap κ α := {
    consts, ownedKeys := owned.map (·.1), ownedVals := owned.map (·.2)
    size := owned.foldl (· + ·.1.size) 0 }
  for es in foreign do
    for (k, v) in es do
      unless m.foreign.contains k || (findOwned? m k).isSome do
        m := { m with size := m.size + 1 }
      m := { m with foreign := m.foreign.insert k v }
  return m

public def find? (m : ImportedDeclMap κ α) (k : κ) : Option α :=
  m.foreign.find? k <|> findOwned? m k

public def contains (m : ImportedDeclMap κ α) (k : κ) : Bool :=
  (find? m k).isSome

@[specialize] public def foldM [Monad m] (f : β → κ → α → m β) (init : β)
    (d : ImportedDeclMap κ α) : m β := do
  let mut b := init
  for h : i in [0:d.ownedKeys.size] do
    let vs := d.ownedVals[i]?.getD #[]
    for h : j in [0:d.ownedKeys[i].size] do
      let k := d.ownedKeys[i][j]
      unless d.foreign.contains k do
        b ← f b k (vs[j]?.getD default)
  d.foreign.foldlM f b

end ImportedDeclMap

/--
A map keyed by declarations, consisting of entries imported as an `ImportedDeclMap` and the changes
made since.
-/
public structure DeclMap (κ α : Type) [BEq κ] [Hashable κ] where
  imported   : ImportedDeclMap κ α := {}
  /-- The erased imported keys not in `added`. -/
  removed    : PHashSet κ := {}
  /-- The size of `removed`. -/
  numRemoved : Nat := 0
  /-- The entries added since the import, overriding imported ones. -/
  added      : PHashMap κ α := {}
  deriving Inhabited

namespace DeclMap

variable {κ α : Type} [BEq κ] [Hashable κ] [ImportedDeclMap.Key κ] [Inhabited α]

public def find? (m : DeclMap κ α) (k : κ) : Option α :=
  m.added.find? k <|> if m.removed.contains k then none else m.imported.find? k

public def contains (m : DeclMap κ α) (k : κ) : Bool :=
  (m.find? k).isSome

public def insert (m : DeclMap κ α) (k : κ) (v : α) : DeclMap κ α :=
  let m := { m with added := m.added.insert k v }
  if m.removed.contains k then
    { m with removed := m.removed.erase k, numRemoved := m.numRemoved - 1 }
  else
    m

public def erase (m : DeclMap κ α) (k : κ) : DeclMap κ α :=
  let m := { m with added := m.added.erase k }
  if m.imported.contains k && !m.removed.contains k then
    { m with removed := m.removed.insert k, numRemoved := m.numRemoved + 1 }
  else
    m

public def isEmpty (m : DeclMap κ α) : Bool :=
  m.added.isEmpty && m.imported.size == m.numRemoved

@[specialize] public def foldM [Monad m] (f : β → κ → α → m β) (init : β) (d : DeclMap κ α) :
    m β := do
  let b ← d.imported.foldM (init := init) fun b k v =>
    if d.removed.contains k || d.added.contains k then pure b else f b k v
  d.added.foldlM f b

@[inline] public def fold (f : β → κ → α → β) (init : β) (d : DeclMap κ α) : β :=
  Id.run <| d.foldM (pure <| f · · ·) init

public def toList (d : DeclMap κ α) : List (κ × α) :=
  d.fold (init := []) fun l k v => (k, v) :: l

end DeclMap

end Lean
