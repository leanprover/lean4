/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Array.TakeDrop
import Std.Data.DHashMap.Basic
import Std.Data.DHashMap.Internal.HashesTo
import Std.Data.DHashMap.Internal.AssocList.Lemmas

/-!
This is an internal implementation file of the hash map. Users of the hash map should not rely on
the contents of this file.

In this file we define functions for manipulating a hash map based on operations defined in terms of
their buckets. Then we give "model implementations" of the hash map operations in terms of these
basic building blocks and show that the actual operations are equal to the model implementations T
his means that later we will be able to prove properties of the operations by proving general facts
about the basic building blocks.
-/

set_option linter.missingDocs true
set_option autoImplicit false

universe u v w

variable {α : Type u} {β : α → Type v} {γ : Type w} {δ : α → Type w}

open List (Perm perm_append_comm_assoc)

namespace Std.DHashMap.Internal

open Std.DHashMap.Internal.List
open Std.Internal.List
open Std.Internal

/-! # Setting up the infrastructure -/

/-- Internal implementation detail of the hash map -/
def bucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α) :
    AssocList α β :=
  let ⟨i, h⟩ := mkIdx self.size h (hash k)
  self[i]

theorem bucket_eq {α : Type u} {β : α → Type v} [Hashable α] (self : Array (AssocList α β))
  (h : 0 < self.size) (k : α) : bucket self h k =
    haveI := mkIdx self.size h (hash k) |>.2
    self[mkIdx self.size h (hash k) |>.1] := rfl

/-- Internal implementation detail of the hash map -/
def updateBucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α)
    (f : AssocList α β → AssocList α β) : Array (AssocList α β) :=
  let ⟨i, h⟩ := mkIdx self.size h (hash k)
  self.uset i (f self[i]) h

/-- Internal implementation detail of the hash map -/
def updateAllBuckets (self : Array (AssocList α β)) (f : AssocList α β → AssocList α δ) :
    Array (AssocList α δ) :=
  self.map f

/-- Internal implementation detail of the hash map -/
def withComputedSize (self : Array (AssocList α β)) : Raw α β :=
  ⟨computeSize self, self⟩

@[simp]
theorem size_updateBucket [Hashable α] {self : Array (AssocList α β)} {h : 0 < self.size} {k : α}
    {f : AssocList α β → AssocList α β} : (updateBucket self h k f).size = self.size := by
  simp [updateBucket]

@[simp]
theorem size_updateAllBuckets {self : Array (AssocList α β)} {f : AssocList α β → AssocList α δ} :
    (updateAllBuckets self f).size = self.size := by
  simp [updateAllBuckets]

@[simp]
theorem buckets_size_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).2.size = self.size := by
  simp [withComputedSize]

@[simp]
theorem size_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).size = computeSize self := rfl

@[simp]
theorem buckets_withComputedSize {self : Array (AssocList α β)} :
    (withComputedSize self).buckets = self := rfl

@[simp]
theorem bucket_updateBucket [Hashable α] (self : Array (AssocList α β)) (h : 0 < self.size) (k : α)
    (f : AssocList α β → AssocList α β) :
    bucket (updateBucket self h k f) (by simpa using h) k = f (bucket self h k) := by
  unfold bucket updateBucket mkIdx
  simp

theorem exists_bucket_of_uset [BEq α] [Hashable α]
  (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) (d : AssocList α β) :
    ∃ l, Perm (toListModel self) (self[i.toNat].toList ++ l) ∧
      Perm (toListModel (self.uset i d hi)) (d.toList ++ l) ∧
      (∀ [LawfulHashable α], IsHashSelf self →
        ∀ k : α, (mkIdx self.size (by omega) (hash k)).1.toNat = i.toNat →
          containsKey k l = false) := by
  have h₀ : 0 < self.size := by omega
  obtain ⟨l₁, l₂, h₁, h₂, h₃⟩ := Array.exists_of_uset hi
  refine ⟨l₁.flatMap AssocList.toList ++ l₂.flatMap AssocList.toList, ?_, ?_, ?_⟩
  · rw [toListModel, h₁]
    simpa using perm_append_comm_assoc _ _ _
  · rw [toListModel, h₃]
    simpa using perm_append_comm_assoc _ _ _
  · intro _ h k hki
    simp only [containsKey_append, Bool.or_eq_false_iff]
    refine ⟨?_, ?_⟩
    · apply List.containsKey_flatMap_eq_false
      intro j hj
      rw [List.getElem_append_left' (l₂ := self[i] :: l₂), getElem_congr_coll h₁.symm]
      apply (h.hashes_to j _).containsKey_eq_false h₀ k
      omega
    · apply List.containsKey_flatMap_eq_false
      intro j hj
      rw [← List.getElem_cons_succ self[i] _ _
        (by simp only [Array.ugetElem_eq_getElem, List.length_cons]; omega)]
      rw [List.getElem_append_right' l₁, getElem_congr_coll h₁.symm]
      apply (h.hashes_to (j + 1 + l₁.length) _).containsKey_eq_false h₀ k
      omega

theorem exists_bucket_of_update [BEq α] [Hashable α] (m : Array (AssocList α β)) (h : 0 < m.size)
    (k : α) (f : AssocList α β → AssocList α β) :
    ∃ l : List ((a : α) × β a),
      Perm (toListModel m) ((bucket m h k).toList ++ l) ∧
      Perm (toListModel (updateBucket m h k f)) ((f (bucket m h k)).toList ++ l) ∧
      (∀ [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → containsKey k' l = false) := by
  let idx := mkIdx m.size h (hash k)
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_uset m idx.1 idx.2 (f m[idx.1])
  exact ⟨l, h₁, h₂, fun h k' hk' => h₃ h _ (hk' ▸ rfl)⟩

theorem exists_bucket' [BEq α] [Hashable α]
    (self : Array (AssocList α β)) (i : USize) (hi : i.toNat < self.size) :
      ∃ l, Perm (self.toList.flatMap AssocList.toList) (self[i.toNat].toList ++ l) ∧
        (∀ [LawfulHashable α], IsHashSelf self → ∀ k,
          (mkIdx self.size (by omega) (hash k)).1.toNat = i.toNat → containsKey k l = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_uset self i hi .nil
  exact ⟨l, h₁, h₂⟩

theorem exists_bucket [BEq α] [Hashable α]
    (m : Array (AssocList α β)) (h : 0 < m.size) (k : α) :
    ∃ l : List ((a : α) × β a), Perm (toListModel m) ((bucket m h k).toList ++ l) ∧
      (∀ [LawfulHashable α], IsHashSelf m → ∀ k', hash k = hash k' → containsKey k' l = false) := by
  obtain ⟨l, h₁, -, h₂⟩ := exists_bucket_of_update m h k (fun _ => .nil)
  exact ⟨l, h₁, h₂⟩

/-- This is the general theorem used to show that access operations are correct. -/
theorem apply_bucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α] {m : Raw₀ α β}
    (hm : Raw.WFImp m.1) {a : α} {f : AssocList α β → γ} {g : List ((a : α) × β a) → γ}
    (hfg : ∀ {l}, f l = g l.toList) (hg₁ : ∀ {l l'}, DistinctKeys l → Perm l l' → g l = g l')
    (hg₂ : ∀ {l l'}, containsKey a l' = false → g (l ++ l') = g l) :
    f (bucket m.1.buckets m.2 a) = g (toListModel m.1.buckets) := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets m.2 a
  refine Eq.trans ?_ (hg₁ (hm.distinct.perm hl.symm) hl.symm)
  rw [hfg, hg₂]
  exact hlk hm.buckets_hash_self _ rfl

/-- This is the general theorem used to show that access operations involving a proof (like `get`)
are correct. -/
theorem apply_bucket_with_proof {γ : α → Type w} [BEq α] [Hashable α] [PartialEquivBEq α]
    [LawfulHashable α] {m : Raw₀ α β} (hm : Raw.WFImp m.1) (a : α)
    (f : (a : α) → (l : AssocList α β) → l.contains a → γ a)
    (g : (a : α) → (l : List ((a : α) × β a)) → containsKey a l → γ a)
    (hfg : ∀ {a l h}, f a l h = g a l.toList (AssocList.contains_eq.symm.trans h))
    (hg₁ : ∀ {l l' a h}, DistinctKeys l → (hl' : Perm l l') →
      g a l h = g a l' ((List.containsKey_of_perm hl').symm.trans h)) {h h'}
    (hg₂ : ∀ {l l' a h}, (hl' : containsKey a l' = false) →
      g a (l ++ l') h = g a l ((List.containsKey_append_of_not_contains_right hl').symm.trans h)) :
    f a (bucket m.1.buckets m.2 a) h = g a (toListModel m.1.buckets) h' := by
  obtain ⟨l, hl, hlk⟩ := exists_bucket m.1.buckets m.2 a
  refine Eq.trans ?_ (hg₁ hm.distinct hl).symm
  rw [hfg, hg₂]
  exact hlk hm.buckets_hash_self _ rfl

/-- This is the general theorem to show that modification operations are correct. -/
theorem toListModel_updateBucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Raw₀ α β} (hm : Raw.WFImp m.1) {a : α} {f : AssocList α β → AssocList α β}
    {g : List ((a : α) × β a) → List ((a : α) × β a)} (hfg : ∀ {l}, Perm (f l).toList (g l.toList))
    (hg₁ : ∀ {l l'}, DistinctKeys l → Perm l l' → Perm (g l) (g l'))
    (hg₂ : ∀ {l l'}, containsKey a l' = false → g (l ++ l') = g l ++ l') :
    Perm (toListModel (updateBucket m.1.buckets m.2 a f)) (g (toListModel m.1.2)) := by
  obtain ⟨l, h₁, h₂, h₃⟩ := exists_bucket_of_update m.1.buckets m.2 a f
  refine h₂.trans (Perm.trans ?_ (hg₁ hm.distinct h₁).symm)
  refine Perm.append_right l hfg |>.trans ?_
  rw [hg₂]
  exact h₃ hm.buckets_hash_self _ rfl

/-- This is the general theorem to show that mapping operations (like `map` and `filter`) are
correct. -/
theorem toListModel_updateAllBuckets {m : Raw₀ α β} {f : AssocList α β → AssocList α δ}
    {g : List ((a : α) × β a) → List ((a : α) × δ a)}
    (hfg : ∀ {l}, Perm ((f l).toList) (g l.toList))
    (hg : ∀ {l l'}, Perm (g (l ++ l')) (g l ++ g l')) :
    Perm (toListModel (updateAllBuckets m.1.buckets f)) (g (toListModel m.1.2)) := by
  have hg₀ : g [] = [] := by
    rw [← List.length_eq_zero_iff]
    have := (hg (l := []) (l' := [])).length_eq
    rw [List.length_append, List.append_nil] at this
    omega
  rw [updateAllBuckets, toListModel, Array.toList_map, List.flatMap_eq_foldl, List.foldl_map,
    toListModel, List.flatMap_eq_foldl]
  suffices ∀ (l : List (AssocList α β)) (l' : List ((a : α) × δ a)) (l'' : List ((a : α) × β a)),
      Perm (g l'') l' →
      Perm (l.foldl (fun acc a => acc ++ (f a).toList) l')
        (g (l.foldl (fun acc a => acc ++ a.toList) l'')) by
    simpa using this m.1.buckets.toList [] [] (by simp [hg₀])
  rintro l l' l'' h
  induction l generalizing l' l''
  · simpa using h.symm
  · next l t ih =>
    simp only [List.foldl_cons]
    apply ih
    exact hg.trans (Perm.append h hfg.symm)

/-! # IsHashSelf -/

namespace IsHashSelf

@[simp]
theorem replicate [BEq α] [Hashable α] {c : Nat} : IsHashSelf
    (Array.replicate c (AssocList.nil : AssocList α β)) :=
  ⟨by simp⟩

set_option linter.missingDocs false in
@[deprecated replicate (since := "2025-03-18")]
abbrev mkArray := @replicate

theorem uset [BEq α] [Hashable α] {m : Array (AssocList α β)} {i : USize} {h : i.toNat < m.size}
    {d : AssocList α β}
    (hd : HashesTo m[i].toList i.toNat m.size → HashesTo d.toList i.toNat m.size)
    (hm : IsHashSelf m) : IsHashSelf (m.uset i d h) := by
  refine ⟨fun j hj => ?_⟩
  simp only [Array.uset, Array.getElem_set, Array.size_set]
  split
  · next hij => exact hij ▸ (hd (hm.hashes_to _ _))
  · exact hm.hashes_to j (by simpa using hj)

/-- This is the general theorem to show that modification operations preserve well-formedness of
buckets. -/
theorem updateBucket [BEq α] [Hashable α] [PartialEquivBEq α] [LawfulHashable α]
    {m : Array (AssocList α β)} {h : 0 < m.size} {a : α} {f : AssocList α β → AssocList α β}
    (hf : ∀ l p, p ∈ (f l).toList → containsKey p.1 l.toList ∨ hash p.1 = hash a)
    (hm : IsHashSelf m) : IsHashSelf (updateBucket m h a f) := by
  rw [Internal.updateBucket]
  refine IsHashSelf.uset (fun h' => ⟨fun _ p hp => ?_⟩) hm
  rcases hf _ _ hp with (hf|hf)
  · rw [containsKey_eq_true_iff_exists_mem] at hf
    rcases hf with ⟨q, hq₁, hq₂⟩
    rw [← h'.hash_self h _ hq₁, hash_eq hq₂]
  · rw [hf]

theorem updateAllBuckets [BEq α] [Hashable α] [LawfulHashable α] {m : Array (AssocList α β)}
    {f : AssocList α β → AssocList α δ} (hf : ∀ l p, p ∈ (f l).toList → containsKey p.1 l.toList)
    (hm : IsHashSelf m) : IsHashSelf (updateAllBuckets m f) := by
  rw [Internal.updateAllBuckets]
  refine ⟨fun j hj => ?_⟩
  simp only [Array.getElem_map, Array.size_map]
  refine ⟨fun h p hp => ?_⟩
  rcases containsKey_eq_true_iff_exists_mem.1 (hf _ _ hp) with ⟨q, hq₁, hq₂⟩
  rw [← hash_eq hq₂, (hm.hashes_to _ _).hash_self _ _ hq₁]

end IsHashSelf

namespace Raw₀

/-! # Definition of model functions -/

/-- Internal implementation detail of the hash map -/
def replaceₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size, updateBucket m.1.buckets m.2 a (fun l => l.replace a b)⟩, by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def consₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  ⟨⟨m.1.size + 1, updateBucket m.1.buckets m.2 a (fun l => l.cons a b)⟩, by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def get?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option (β a) :=
  (bucket m.1.buckets m.2 a).getCast? a

/-- Internal implementation detail of the hash map -/
def getKey?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Option α :=
  (bucket m.1.buckets m.2 a).getKey? a

/-- Internal implementation detail of the hash map -/
def containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Bool :=
  (bucket m.1.buckets m.2 a).contains a

/-- Internal implementation detail of the hash map -/
def getₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.containsₘ a) : β a :=
  (bucket m.1.buckets m.2 a).getCast a h

/-- Internal implementation detail of the hash map -/
def getDₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : β a) : β a :=
  (m.get?ₘ a).getD fallback

/-- Internal implementation detail of the hash map -/
def get!ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] : β a :=
  (m.get?ₘ a).get!

/-- Internal implementation detail of the hash map -/
def getKeyₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.containsₘ a) : α :=
  (bucket m.1.buckets m.2 a).getKey a h

/-- Internal implementation detail of the hash map -/
def getKeyDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : α) : α :=
  (m.getKey?ₘ a).getD fallback

/-- Internal implementation detail of the hash map -/
def getKey!ₘ [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) : α :=
  (m.getKey?ₘ a).get!

/-- Internal implementation detail of the hash map -/
def insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  if m.containsₘ a then m.replaceₘ a b else Raw₀.expandIfNecessary (m.consₘ a b)

/-- Internal implementation detail of the hash map -/
def insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) : Raw₀ α β :=
  if m.containsₘ a then m else Raw₀.expandIfNecessary (m.consₘ a b)

/-- Internal implementation detail of the hash map -/
def eraseₘaux [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  ⟨⟨m.1.size - 1, updateBucket m.1.buckets m.2 a (fun l => l.erase a)⟩, by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) : Raw₀ α β :=
  if m.containsₘ a then m.eraseₘaux a else m

/-- Internal implementation detail of the hash map -/
def alterₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : Option (β a) → Option (β a)) : Raw₀ α β :=
  if h : m.containsₘ a then
    let buckets' := updateBucket m.1.buckets m.2 a (fun l => l.alter a f)
    let size' :=
      if Raw₀.containsₘ ⟨withComputedSize buckets', by simpa [buckets'] using m.2⟩ a
      then m.1.size else m.1.size - 1
    ⟨⟨size', buckets'⟩, by simpa [buckets'] using m.2⟩
  else
    match f none with
    | none => m
    | some b => Raw₀.expandIfNecessary (m.consₘ a b)

/-- Internal implementation detail of the hash map -/
def modifyₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α) (f : β a → β a) : Raw₀ α β :=
  m.alterₘ a (·.map f)

namespace Const

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def alterₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : Option β → Option β) : Raw₀ α (fun _ => β) :=
  if h : m.containsₘ a then
    let buckets' := updateBucket m.1.buckets m.2 a (fun l => AssocList.Const.alter a f l)
    let size' :=
      if Raw₀.containsₘ ⟨withComputedSize buckets', by simpa [buckets'] using m.2⟩ a
      then m.1.size else m.1.size - 1
    ⟨⟨size', buckets'⟩, by simpa [buckets'] using m.2⟩
  else
    match f none with
    | none => m
    | some b => Raw₀.expandIfNecessary (m.consₘ a b)

/-- Internal implementation detail of the hash map -/
def modifyₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (f : β → β) :
    Raw₀ α (fun _ => β) :=
  alterₘ m a (fun option => option.map f)

end Const

/-- Internal implementation detail of the hash map -/
def filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) : Raw₀ α δ :=
  ⟨withComputedSize (updateAllBuckets m.1.buckets fun l => l.filterMap f), by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) : Raw₀ α δ :=
  ⟨⟨m.1.size, updateAllBuckets m.1.buckets (AssocList.map f)⟩, by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def filterₘ (m : Raw₀ α β) (f : (a : α) → β a → Bool) : Raw₀ α β :=
  ⟨withComputedSize (updateAllBuckets m.1.buckets fun l => l.filter f), by simpa using m.2⟩

/-- Internal implementation detail of the hash map -/
def insertListₘ [BEq α] [Hashable α] (m : Raw₀ α β) (l : List ((a : α) × β a)) : Raw₀ α β :=
  match l with
  | .nil => m
  | .cons hd tl => insertListₘ (m.insert hd.1 hd.2) tl

section

variable {β : Type v}

/-- Internal implementation detail of the hash map -/
def Const.get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) : Option β :=
  (bucket m.1.buckets m.2 a).get? a

/-- Internal implementation detail of the hash map -/
def Const.getₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (h : m.containsₘ a) : β :=
  (bucket m.1.buckets m.2 a).get a h

/-- Internal implementation detail of the hash map -/
def Const.getDₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fallback : β) : β :=
  (Const.get?ₘ m a).getD fallback

/-- Internal implementation detail of the hash map -/
def Const.get!ₘ [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) : β :=
  (Const.get?ₘ m a).get!

/-- Internal implementation detail of the hash map -/
def Const.insertListₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (l: List (α × β)) :
    Raw₀ α (fun _ => β) :=
  match l with
  | .nil => m
  | .cons hd tl => insertListₘ (m.insert hd.1 hd.2) tl

/-- Internal implementation detail of the hash map -/
def Const.insertListIfNewUnitₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => Unit)) (l: List α) :
    Raw₀ α (fun _ => Unit) :=
  match l with
  | .nil => m
  | .cons hd tl => insertListIfNewUnitₘ (m.insertIfNew hd ()) tl

end

/-! # Equivalence between model functions and real implementations -/

theorem reinsertAux_eq [Hashable α] (data : { d : Array (AssocList α β) // 0 < d.size }) (a : α)
    (b : β a) :
    (reinsertAux hash data a b).1 = updateBucket data.1 data.2 a (fun l => l.cons a b) := rfl

theorem get?_eq_get?ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    get? m a = get?ₘ m a := rfl

theorem get_eq_getₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.contains a) :
    get m a h = getₘ m a h := rfl

theorem getD_eq_getDₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) (fallback : β a) :
    getD m a fallback = getDₘ m a fallback := by
  simp [getD, getDₘ, get?ₘ, List.getValueCastD_eq_getValueCast?, bucket]

theorem get!_eq_get!ₘ [BEq α] [LawfulBEq α] [Hashable α] (m : Raw₀ α β) (a : α) [Inhabited (β a)] :
    get! m a = get!ₘ m a := by
  simp [get!, get!ₘ, get?ₘ, List.getValueCast!_eq_getValueCast?, bucket]

theorem getKey?_eq_getKey?ₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    getKey? m a = getKey?ₘ m a := rfl

theorem getKey_eq_getKeyₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (h : m.contains a) :
    getKey m a h = getKeyₘ m a h := rfl

theorem getKeyD_eq_getKeyDₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a fallback : α) :
    getKeyD m a fallback = getKeyDₘ m a fallback := by
  simp [getKeyD, getKeyDₘ, getKey?ₘ, List.getKeyD_eq_getKey?, bucket]

theorem getKey!_eq_getKey!ₘ [BEq α] [Hashable α] [Inhabited α] (m : Raw₀ α β) (a : α) :
    getKey! m a = getKey!ₘ m a := by
  simp [getKey!, getKey!ₘ, getKey?ₘ, List.getKey!_eq_getKey?, bucket]

theorem contains_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.contains a = m.containsₘ a := rfl

theorem insert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.insert a b = m.insertₘ a b := by
  rw [insert, insertₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split
  · simp only [replaceₘ, Subtype.mk.injEq, Raw.mk.injEq, true_and]
    rw [Array.set_set, updateBucket]
    simp only [Array.uset, Array.ugetElem_eq_getElem]
  · rfl

theorem alter_eq_alterₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : Option (β a) → Option (β a)) : m.alter a f = m.alterₘ a f := by
    dsimp only [alter, alterₘ, containsₘ, ← bucket_eq]
    split
    · congr 2
      · simp only [withComputedSize, bucket_updateBucket]
      · simp only [Array.uset, bucket, Array.ugetElem_eq_getElem, Array.set_set, updateBucket]
    · congr

theorem modify_eq_alter [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : β a → β a) : m.modify a f = m.alter a (·.map f) := by
  rw [modify, alter]
  split
  · dsimp
    split
    · next h =>
      simp only [AssocList.contains_eq] at h
      simp only [AssocList.modify_eq_alter, Array.set_set, AssocList.contains_eq,
        containsKey_of_perm AssocList.toList_alter, ← modifyKey_eq_alterKey,
        containsKey_modifyKey, h, reduceIte]
    · rfl

theorem modify_eq_modifyₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (f : β a → β a) : m.modify a f = m.modifyₘ a f := by
  rw [modify_eq_alter, alter_eq_alterₘ, modifyₘ]

namespace Const

variable {β : Type v}

theorem alter_eq_alterₘ [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : Option β → Option β) : Const.alter m a f = Const.alterₘ m a f := by
    dsimp only [alter, alterₘ, containsₘ, ← bucket_eq]
    split
    · congr 2
      · simp only [withComputedSize, bucket_updateBucket]
      · simp only [Array.uset, bucket, Array.ugetElem_eq_getElem, Array.set_set, updateBucket]
    · congr

theorem modify_eq_alter [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : β → β) : Const.modify m a f = Const.alter m a (·.map f) := by
  rw [modify, alter]
  split
  · dsimp
    split
    · next h =>
      simp only [AssocList.contains_eq] at h
      simp only [AssocList.Const.modify_eq_alter, Array.set_set, AssocList.contains_eq,
        containsKey_of_perm AssocList.Const.toList_alter, ← Const.modifyKey_eq_alterKey,
        Const.containsKey_modifyKey, h, reduceIte]
    · rfl

theorem modify_eq_modifyₘ [BEq α] [Hashable α] [EquivBEq α] (m : Raw₀ α (fun _ => β)) (a : α)
    (f : β → β) : Const.modify m a f = Const.modifyₘ m a f := by
  rw [modify_eq_alter, alter_eq_alterₘ, modifyₘ]

end Const

theorem containsThenInsert_eq_insertₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.containsThenInsert a b).2 = m.insertₘ a b := by
  rw [containsThenInsert, insertₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split
  · simp only [replaceₘ, Subtype.mk.injEq, Raw.mk.injEq, true_and]
    rw [Array.set_set, updateBucket]
    simp only [Array.uset, Array.ugetElem_eq_getElem]
  · rfl

theorem containsThenInsert_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.containsThenInsert a b).1 = m.containsₘ a := by
  rw [containsThenInsert, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all

theorem containsThenInsertIfNew_eq_insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α)
    (b : β a) : (m.containsThenInsertIfNew a b).2 = m.insertIfNewₘ a b := by
  rw [containsThenInsertIfNew, insertIfNewₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split
  · simp only [replaceₘ, Subtype.mk.injEq, Raw.mk.injEq, true_and]
  · rfl

theorem containsThenInsertIfNew_eq_containsₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    (m.containsThenInsertIfNew a b).1 = m.containsₘ a := by
  rw [containsThenInsertIfNew, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all

theorem insertIfNew_eq_insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) (b : β a) :
    m.insertIfNew a b = m.insertIfNewₘ a b := rfl

theorem getThenInsertIfNew?_eq_insertIfNewₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β)
    (a : α) (b : β a) : (m.getThenInsertIfNew? a b).2 = m.insertIfNewₘ a b := by
  rw [getThenInsertIfNew?, insertIfNewₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all [consₘ, updateBucket, List.containsKey_eq_isSome_getValueCast?]

theorem getThenInsertIfNew?_eq_get?ₘ [BEq α] [Hashable α] [LawfulBEq α] (m : Raw₀ α β) (a : α)
    (b : β a) : (m.getThenInsertIfNew? a b).1 = m.get?ₘ a := by
  rw [getThenInsertIfNew?, get?ₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all

theorem erase_eq_eraseₘ [BEq α] [Hashable α] (m : Raw₀ α β) (a : α) :
    m.erase a = m.eraseₘ a := by
  rw [erase, eraseₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split
  · simp only [eraseₘaux, Subtype.mk.injEq, Raw.mk.injEq, true_and]
    rw [Array.set_set, updateBucket]
    simp only [Array.uset, Array.ugetElem_eq_getElem]
  · rfl

theorem filterMap_eq_filterMapₘ (m : Raw₀ α β) (f : (a : α) → β a → Option (δ a)) :
    m.filterMap f = m.filterMapₘ f := rfl

theorem map_eq_mapₘ (m : Raw₀ α β) (f : (a : α) → β a → δ a) :
    m.map f = m.mapₘ f := rfl

theorem filter_eq_filterₘ (m : Raw₀ α β) (f : (a : α) → β a → Bool) :
    m.filter f = m.filterₘ f := rfl

theorem insertMany_eq_insertListₘ [BEq α] [Hashable α](m : Raw₀ α β) (l : List ((a : α) × β a)) : insertMany m l = insertListₘ m l := by
  simp only [insertMany, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α β → Prop),
    (∀ {m'' : Raw₀ α β} {a : α} {b : β a}, P m'' → P (m''.insert a b)) → P m → P m' }),
      (List.foldl (fun m' p => ⟨m'.val.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
    t.val.insertListₘ l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListₘ]
    apply ih

section

variable {β : Type v}

theorem Const.get?_eq_get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) :
    Const.get? m a = Const.get?ₘ m a := rfl

theorem Const.get_eq_getₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (h : m.contains a) : Const.get m a h = Const.getₘ m a h := rfl

theorem Const.getD_eq_getDₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α) (fallback : β) :
    Const.getD m a fallback = Const.getDₘ m a fallback := by
  simp [getD, getDₘ, get?ₘ, List.getValueD_eq_getValue?, bucket]

theorem Const.get!_eq_get!ₘ [BEq α] [Hashable α] [Inhabited β] (m : Raw₀ α (fun _ => β)) (a : α) :
    Const.get! m a = Const.get!ₘ m a := by
  simp [get!, get!ₘ, get?ₘ, List.getValue!_eq_getValue?, bucket]

theorem Const.getThenInsertIfNew?_eq_insertIfNewₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (a : α) (b : β) : (Const.getThenInsertIfNew? m a b).2 = m.insertIfNewₘ a b := by
  rw [getThenInsertIfNew?, insertIfNewₘ, containsₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all [consₘ, updateBucket, List.containsKey_eq_isSome_getValue?, -Option.not_isSome]

theorem Const.getThenInsertIfNew?_eq_get?ₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β)) (a : α)
    (b : β) : (Const.getThenInsertIfNew? m a b).1 = Const.get?ₘ m a := by
  rw [getThenInsertIfNew?, get?ₘ, bucket]
  dsimp only [Array.ugetElem_eq_getElem, Array.uset]
  split <;> simp_all [-getValue?_eq_none]

theorem Const.insertMany_eq_insertListₘ [BEq α] [Hashable α] (m : Raw₀ α (fun _ => β))
    (l: List (α × β)):
    (Const.insertMany m l).1 = Const.insertListₘ m l := by
  simp only [insertMany, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α (fun _ => β) → Prop),
    (∀ {m'' : Raw₀ α (fun _ => β)} {a : α} {b : β}, P m'' → P (m''.insert a b)) → P m → P m' }),
      (List.foldl (fun m' p => ⟨m'.val.insert p.1 p.2, fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
    Const.insertListₘ t.val l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListₘ]
    apply ih

theorem Const.insertManyIfNewUnit_eq_insertListIfNewUnitₘ [BEq α] [Hashable α]
    (m : Raw₀ α (fun _ => Unit)) (l: List α):
    (Const.insertManyIfNewUnit m l).1 = Const.insertListIfNewUnitₘ m l := by
  simp only [insertManyIfNewUnit, Id.run, Id.pure_eq, Id.bind_eq, List.forIn_yield_eq_foldl]
  suffices ∀ (t : { m' // ∀ (P : Raw₀ α (fun _ => Unit) → Prop),
      (∀ {m'' a b}, P m'' → P (m''.insertIfNew a b)) → P m → P m'}),
      (List.foldl (fun m' p => ⟨m'.val.insertIfNew p (), fun P h₁ h₂ => h₁ (m'.2 _ h₁ h₂)⟩) t l).val =
    Const.insertListIfNewUnitₘ t.val l from this _
  intro t
  induction l generalizing m with
  | nil => simp [insertListIfNewUnitₘ]
  | cons hd tl ih =>
    simp only [List.foldl_cons, insertListIfNewUnitₘ]
    apply ih

end

end Raw₀

end Std.DHashMap.Internal
