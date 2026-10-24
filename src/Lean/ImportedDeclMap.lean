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
  /-- Per module index, the entries owned by the module (see `isOwnedBy`), sorted by key. -/
  owned   : Array (Array (κ × α)) := #[]
  /-- The entries not owned by the module declaring their constant; they override owned entries. -/
  foreign : PHashMap κ α := {}
  /-- The number of keys. -/
  size    : Nat := 0
  deriving Inhabited

namespace ImportedDeclMap

variable {κ α : Type} [BEq κ] [Hashable κ] [Key κ] [Inhabited α]

/--
Whether the module with index `modIdx?` (the current module if `none`) owns an entry about constant
`n`: it declares `n`, which does not have a reserved name. Constants with reserved names, such as
equational theorems, may be realized by several modules.
-/
public def isOwnedBy (env : Environment) (modIdx? : Option ModuleIdx) (n : Name) : Bool :=
  (env.getModuleIdxFor? n).map (·.toNat) == modIdx?.map (·.toNat) && !isReservedName env n

/-- Sorts the entries a module owns by key, keeping the last entry of each key. -/
public def sortOwned (es : Array (κ × α)) : Array (κ × α) :=
  let es := es.mapIdx fun i e => (i, e)
  let es := es.qsort fun (i₁, k₁, _) (i₂, k₂, _) => Key.lt k₁ k₂ || (k₁ == k₂ && i₁ > i₂)
  es.foldl (init := #[]) fun out (_, k, v) =>
    if out.back?.any (·.1 == k) then out else out.push (k, v)

def findOwned? (m : ImportedDeclMap κ α) (k : κ) : Option α :=
  if m.owned.isEmpty then none
  else match m.consts.findConstModIdxCached? (Key.declName k) with
    | some i => (m.owned[i]?.getD #[]).binSearch (k, default) (Key.lt ·.1 ·.1) |>.map (·.2)
    | none => none

/--
Assembles the imported entries of all modules, given in module order: those owned by a module, as
returned by `sortOwned`, at the module's index, and the remaining ones, of which later ones override
earlier ones.
-/
public def ofModules (consts : ImportedConsts ConstantInfo) (owned : Array (Array (κ × α)))
    (foreign : Array (Array (κ × α))) : ImportedDeclMap κ α := Id.run do
  let mut m : ImportedDeclMap κ α := { consts, owned, size := owned.foldl (· + ·.size) 0 }
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
  let b ← d.owned.foldlM (init := init) fun b es =>
    es.foldlM (init := b) fun b (k, v) => if d.foreign.contains k then pure b else f b k v
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
