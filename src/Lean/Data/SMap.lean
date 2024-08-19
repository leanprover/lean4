/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Std.Data.HashMap.Basic
import Lean.Data.HashMap
import Lean.Data.PersistentHashMap
universe u v w w'

namespace Lean

/-- Staged map for implementing the Environment. The idea is to store
   imported entries into a hashtable and local entries into a persistent hashtable.

   Hypotheses:
   - The number of entries (i.e., declarations) coming from imported files is much bigger than
     the number of entries in the current file.
   - HashMap is faster than PersistentHashMap.
   - When we are reading imported files, we have exclusive access to the map, and efficient
     destructive updates are performed.

   Remarks:
   - We never remove declarations from the Environment. In principle, we could support
     deletion by using `(PHashMap α (Option β))` where the value `none` would indicate
     that an entry was "removed" from the hashtable.
   - We do not need additional bookkeeping for extracting the local entries.
-/
structure SMap (α : Type u) (β : Type v) [BEq α] [Hashable α] where
  stage₁ : Bool         := true
  map₁   : Std.HashMap α β  := {}
  map₂   : PHashMap α β := {}

namespace SMap
variable {α : Type u} {β : Type v} [BEq α] [Hashable α]

instance : Inhabited (SMap α β) := ⟨{}⟩
def empty : SMap α β := {}

@[inline] def fromHashMap (m : Std.HashMap α β) (stage₁ := true) : SMap α β :=
  { map₁ := m, stage₁ := stage₁ }

@[specialize] def insert : SMap α β → α → β → SMap α β
  | ⟨true, m₁, m₂⟩, k, v  => ⟨true, m₁.insert k v, m₂⟩
  | ⟨false, m₁, m₂⟩, k, v => ⟨false, m₁, m₂.insert k v⟩

@[specialize] def insert' : SMap α β → α → β → SMap α β
  | ⟨true, m₁, m₂⟩, k, v  => ⟨true, m₁.insert k v, m₂⟩
  | ⟨false, m₁, m₂⟩, k, v => ⟨false, m₁, m₂.insert k v⟩

@[specialize] def find? : SMap α β → α → Option β
  | ⟨true, m₁, _⟩, k   => m₁[k]?
  | ⟨false, m₁, m₂⟩, k => (m₂.find? k).orElse fun _ => m₁[k]?

@[inline] def findD (m : SMap α β) (a : α) (b₀ : β) : β :=
  (m.find? a).getD b₀

@[inline] def find! [Inhabited β] (m : SMap α β) (a : α) : β :=
  match m.find? a with
  | some b => b
  | none   => panic! "key is not in the map"

@[specialize] def contains : SMap α β → α → Bool
  | ⟨true, m₁, _⟩, k   => m₁.contains k
  | ⟨false, m₁, m₂⟩, k => m₁.contains k || m₂.contains k

/-- Similar to `find?`, but searches for result in the hashmap first.
   So, the result is correct only if we never "overwrite" `map₁` entries using `map₂`. -/
@[specialize] def find?' : SMap α β → α → Option β
  | ⟨true, m₁, _⟩, k   => m₁[k]?
  | ⟨false, m₁, m₂⟩, k => m₁[k]?.orElse fun _ => m₂.find? k

def forM [Monad m] (s : SMap α β) (f : α → β → m PUnit) : m PUnit := do
  s.map₁.forM f
  s.map₂.forM f

instance : ForM m (SMap α β) (α × β) where
  forM s f := forM s fun x y => f (x, y)

instance : ForIn m (SMap α β) (α × β) where
  forIn := ForM.forIn

/-- Move from stage 1 into stage 2. -/
def switch (m : SMap α β) : SMap α β :=
  if m.stage₁ then { m with stage₁ := false } else m

@[inline] def foldStage2 {σ : Type w} (f : σ → α → β → σ) (s : σ) (m : SMap α β) : σ :=
  m.map₂.foldl f s

/-- Monadic fold over a staged map. -/
def foldM {m : Type w → Type w} [Monad m]
    (f : σ → α → β → m σ) (init : σ) (map : SMap α β) : m σ := do
  map.map₂.foldlM f (← map.map₁.foldM f init)

def fold {σ : Type w} (f : σ → α → β → σ) (init : σ) (m : SMap α β) : σ :=
  m.map₂.foldl f $ m.map₁.fold f init

def numBuckets (m : SMap α β) : Nat :=
  Std.HashMap.Internal.numBuckets m.map₁

def toList (m : SMap α β) : List (α × β) :=
  m.fold (init := []) fun es a b => (a, b)::es

end SMap

def _root_.List.toSMap [BEq α] [Hashable α] (es : List (α × β)) : SMap α β :=
  es.foldl (init := {}) fun s (a, b) => s.insert a b

instance {_ : BEq α} {_ : Hashable α} [Repr α] [Repr β] : Repr (SMap α β) where
  reprPrec v prec := Repr.addAppParen (reprArg v.toList ++ ".toSMap") prec

end Lean
