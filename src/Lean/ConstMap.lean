/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.ConstTrie
public import Lean.Declaration
public import Lean.Data.PersistentHashMap

namespace Lean

namespace ImportedConsts

@[export lean_imported_consts_find_entry_core]
def findEntryCore (t : ImportedConsts ConstantInfo) (n : Name) :
    Option (ConstantInfo × Nat) :=
  t.findEntry? n

/-- `findExtraEntryCachedImpl` for `constants.map₁`. -/
@[extern "lean_imported_consts_find_entry_cached"]
opaque findConstEntryCachedImpl (cache? : @& Option LookupCache)
    (t : @& ImportedConsts ConstantInfo) (n : @& Name) : Option (ConstantInfo × Nat)

/-- `findExtraEntryCached?` for `constants.map₁`. -/
@[inline] public def findConstEntryCached? (t : ImportedConsts ConstantInfo) (n : Name) :
    Option (ConstantInfo × Nat) :=
  findConstEntryCachedImpl t.cache? t n

@[inherit_doc findConstEntryCached?, inline]
public def findConstCached? (t : ImportedConsts ConstantInfo) (n : Name) : Option ConstantInfo :=
  (t.findConstEntryCached? n).map (·.1)

/--
The module index of `findConstEntryCached?` plus one, or zero if not found; returning a scalar avoids
reference counting on hits.
-/
@[extern "lean_imported_consts_find_mod_idx_cached"]
opaque findConstModIdxCachedImpl (cache? : @& Option LookupCache)
    (t : @& ImportedConsts ConstantInfo) (n : @& Name) : Nat

@[inherit_doc findConstEntryCached?, inline]
public def findConstModIdxCached? (t : ImportedConsts ConstantInfo) (n : Name) : Option Nat :=
  match findConstModIdxCachedImpl t.cache? t n with
  | 0 => none
  | i + 1 => some i

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
  m.map₂.find? n <|> m.map₁.findConstCached? n

/--
Similar to `find?`, but searches the imported constants first. So, the result is correct only if
imported constants are never overwritten.
-/
public def find?' (m : ConstMap) (n : Name) : Option ConstantInfo :=
  m.map₁.findConstCached? n <|> m.map₂.find? n

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
