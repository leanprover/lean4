/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
namespace Std
universe u v w

def HashSetBucket (α : Type u) :=
  { b : Array (List α) // b.size > 0 }

def HashSetBucket.update {α : Type u} (data : HashSetBucket α) (i : USize) (d : List α) (h : i.toNat < data.val.size) : HashSetBucket α :=
  ⟨ data.val.uset i d h,
    by erw [Array.size_set]; apply data.property ⟩

structure HashSetImp (α : Type u) where
  size       : Nat
  buckets    : HashSetBucket α

def mkHashSetImp {α : Type u} (nbuckets := 8) : HashSetImp α :=
  let n := if nbuckets = 0 then 8 else nbuckets
  { size       := 0,
    buckets    :=
    ⟨ mkArray n [],
      by rw [Array.size_mkArray]; cases nbuckets; decide; apply Nat.zero_lt_succ ⟩ }

namespace HashSetImp
variable {α : Type u}

def mkIdx {n : Nat} (h : n > 0) (u : USize) : { u : USize // u.toNat < n } :=
  ⟨u % n, USize.modn_lt _ h⟩

@[inline] def reinsertAux (hashFn : α → UInt64) (data : HashSetBucket α) (a : α) : HashSetBucket α :=
  let ⟨i, h⟩ := mkIdx data.property (hashFn a |>.toUSize)
  data.update i (a :: data.val.uget i h) h

@[inline] def foldBucketsM {δ : Type w} {m : Type w → Type w} [Monad m] (data : HashSetBucket α) (d : δ) (f : δ → α → m δ) : m δ :=
  data.val.foldlM (init := d) fun d as => as.foldlM f d

@[inline] def foldBuckets {δ : Type w} (data : HashSetBucket α) (d : δ) (f : δ → α → δ) : δ :=
  Id.run $ foldBucketsM data d f

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → m δ) (d : δ) (h : HashSetImp α) : m δ :=
  foldBucketsM h.buckets d f

@[inline] def fold {δ : Type w} (f : δ → α → δ) (d : δ) (m : HashSetImp α) : δ :=
  foldBuckets m.buckets d f

def find? [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : Option α :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a |>.toUSize)
    (buckets.val.uget i h).find? (fun a' => a == a')

def contains [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : Bool :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a |>.toUSize)
    (buckets.val.uget i h).contains a

-- TODO: remove `partial` by using well-founded recursion
partial def moveEntries [Hashable α] (i : Nat) (source : Array (List α)) (target : HashSetBucket α) : HashSetBucket α :=
  if h : i < source.size then
     let idx : Fin source.size := ⟨i, h⟩
     let es  : List α   := source.get idx
     -- We remove `es` from `source` to make sure we can reuse its memory cells when performing es.foldl
     let source                := source.set idx []
     let target                := es.foldl (reinsertAux hash) target
     moveEntries (i+1) source target
  else target

def expand [Hashable α] (size : Nat) (buckets : HashSetBucket α) : HashSetImp α :=
  let nbuckets := buckets.val.size * 2
  have : nbuckets > 0 := Nat.mul_pos buckets.property (by decide)
  let new_buckets : HashSetBucket α := ⟨mkArray nbuckets [], by rw [Array.size_mkArray]; assumption⟩
  { size    := size,
    buckets := moveEntries 0 buckets.val new_buckets }

def insert [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : HashSetImp α :=
  match m with
  | ⟨size, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a |>.toUSize)
    let bkt    := buckets.val.uget i h
    if bkt.contains a
    then ⟨size, buckets.update i (bkt.replace a a) h⟩
    else
      let size'    := size + 1
      let buckets' := buckets.update i (a :: bkt) h
      if size' ≤ buckets.val.size
      then { size := size', buckets := buckets' }
      else expand size' buckets'

def erase [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : HashSetImp α :=
  match m with
  | ⟨ size, buckets ⟩ =>
    let ⟨i, h⟩ := mkIdx buckets.property (hash a |>.toUSize)
    let bkt    := buckets.val.uget i h
    if bkt.contains a then ⟨size - 1, buckets.update i (bkt.erase a) h⟩
    else m

inductive WellFormed [BEq α] [Hashable α] : HashSetImp α → Prop where
  | mkWff     : ∀ n,                  WellFormed (mkHashSetImp n)
  | insertWff : ∀ m a, WellFormed m → WellFormed (insert m a)
  | eraseWff  : ∀ m a, WellFormed m → WellFormed (erase m a)

end HashSetImp

def HashSet (α : Type u) [BEq α] [Hashable α] :=
  { m : HashSetImp α // m.WellFormed }

open HashSetImp

def mkHashSet {α : Type u} [BEq α] [Hashable α] (nbuckets := 8) : HashSet α :=
  ⟨ mkHashSetImp nbuckets, WellFormed.mkWff nbuckets ⟩

namespace HashSet
@[inline] def empty [BEq α] [Hashable α] : HashSet α :=
  mkHashSet

instance [BEq α] [Hashable α] : Inhabited (HashSet α) where
  default := mkHashSet

instance [BEq α] [Hashable α] : EmptyCollection (HashSet α) := ⟨mkHashSet⟩

variable {α : Type u} {_ : BEq α} {_ : Hashable α}

@[inline] def insert (m : HashSet α) (a : α) : HashSet α :=
  match m with
  | ⟨ m, hw ⟩ => ⟨ m.insert a, WellFormed.insertWff m a hw ⟩

@[inline] def erase (m : HashSet α) (a : α) : HashSet α :=
  match m with
  | ⟨ m, hw ⟩ => ⟨ m.erase a, WellFormed.eraseWff m a hw ⟩

@[inline] def find? (m : HashSet α) (a : α) : Option α :=
  match m with
  | ⟨ m, _ ⟩ => m.find? a

@[inline] def contains (m : HashSet α) (a : α) : Bool :=
  match m with
  | ⟨ m, _ ⟩ => m.contains a

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → m δ) (init : δ) (h : HashSet α) : m δ :=
  match h with
  | ⟨ h, _ ⟩ => h.foldM f init

@[inline] def fold {δ : Type w} (f : δ → α → δ) (init : δ) (m : HashSet α) : δ :=
  match m with
  | ⟨ m, _ ⟩ => m.fold f init

@[inline] def size (m : HashSet α) : Nat :=
  match m with
  | ⟨ {size := sz, ..}, _ ⟩ => sz

@[inline] def isEmpty (m : HashSet α) : Bool :=
  m.size = 0

def toList (m : HashSet α) : List α :=
  m.fold (init := []) fun r a => a::r

def toArray (m : HashSet α) : Array α :=
  m.fold (init := #[]) fun r a => r.push a

def numBuckets (m : HashSet α) : Nat :=
  m.val.buckets.val.size

end HashSet
end Std
