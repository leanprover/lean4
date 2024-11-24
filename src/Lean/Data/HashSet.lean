/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Power2
import Std.Data.HashSet.Basic
import Std.Data.HashSet.Raw
namespace Lean
universe u v w

def HashSetBucket (α : Type u) :=
  { b : Array (List α) // b.size.isPowerOfTwo }

def HashSetBucket.update {α : Type u} (data : HashSetBucket α) (i : USize) (d : List α) (h : i.toNat < data.val.size) : HashSetBucket α :=
  ⟨ data.val.uset i d h,
    by erw [Array.size_set]; apply data.property ⟩

@[simp] theorem HashSetBucket.size_update {α : Type u} (data : HashSetBucket α) (i : USize) (d : List α) (h : i.toNat < data.val.size) :
    (data.update i d h).val.size = data.val.size := by
  simp [update, Array.uset]

structure HashSetImp (α : Type u) where
  size       : Nat
  buckets    : HashSetBucket α

def mkHashSetImp {α : Type u} (capacity := 8) : HashSetImp α :=
  { size       := 0
    buckets    :=
    ⟨mkArray ((capacity * 4) / 3).nextPowerOfTwo [],
     by simp; apply Nat.isPowerOfTwo_nextPowerOfTwo⟩ }

namespace HashSetImp
variable {α : Type u}

/- Remark: we use a C implementation because this function is performance critical. -/
@[extern "lean_hashset_mk_idx"]
private def mkIdx {sz : Nat} (hash : UInt64) (h : sz.isPowerOfTwo) : { u : USize // u.toNat < sz } :=
  -- TODO: avoid `if` in the reference implementation
  let u := hash.toUSize &&& (sz.toUSize - 1)
  if h' : u.toNat < sz then
    ⟨u, h'⟩
  else
    ⟨0, by simp; apply Nat.pos_of_isPowerOfTwo h⟩

@[inline] def reinsertAux (hashFn : α → UInt64) (data : HashSetBucket α) (a : α) : HashSetBucket α :=
  let ⟨i, h⟩ := mkIdx (hashFn a) data.property
  data.update i (a :: data.val[i]) h

@[inline] def foldBucketsM {δ : Type w} {m : Type w → Type w} [Monad m] (data : HashSetBucket α) (d : δ) (f : δ → α → m δ) : m δ :=
  data.val.foldlM (init := d) fun d as => as.foldlM f d

@[inline] def foldBuckets {δ : Type w} (data : HashSetBucket α) (d : δ) (f : δ → α → δ) : δ :=
  Id.run $ foldBucketsM data d f

@[inline] def foldM {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → m δ) (d : δ) (h : HashSetImp α) : m δ :=
  foldBucketsM h.buckets d f

@[inline] def fold {δ : Type w} (f : δ → α → δ) (d : δ) (m : HashSetImp α) : δ :=
  foldBuckets m.buckets d f

@[inline] def forBucketsM {m : Type w → Type w} [Monad m] (data : HashSetBucket α) (f : α → m PUnit) : m PUnit :=
  data.val.forM fun as => as.forM f

@[inline] def forM {m : Type w → Type w} [Monad m] (f : α → m PUnit) (h : HashSetImp α) : m PUnit :=
  forBucketsM h.buckets f

def find? [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : Option α :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    buckets.val[i].find? (fun a' => a == a')

def contains [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : Bool :=
  match m with
  | ⟨_, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    buckets.val[i].contains a

def moveEntries [Hashable α] (i : Nat) (source : Array (List α)) (target : HashSetBucket α) : HashSetBucket α :=
  if h : i < source.size then
     let es  : List α   := source[i]
     -- We remove `es` from `source` to make sure we can reuse its memory cells when performing es.foldl
     let source                := source.set i []
     let target                := es.foldl (reinsertAux hash) target
     moveEntries (i+1) source target
  else
    target
termination_by source.size - i
decreasing_by simp_wf; decreasing_trivial_pre_omega

def expand [Hashable α] (size : Nat) (buckets : HashSetBucket α) : HashSetImp α :=
  let bucketsNew : HashSetBucket α := ⟨
    mkArray (buckets.val.size * 2) [],
    by simp; apply Nat.mul2_isPowerOfTwo_of_isPowerOfTwo buckets.property
  ⟩
  { size    := size,
    buckets := moveEntries 0 buckets.val bucketsNew }

def insert [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : HashSetImp α :=
  match m with
  | ⟨size, buckets⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    let bkt    := buckets.val[i]
    if bkt.contains a
    then
      -- make sure `bkt` is used linearly in the following call to `replace`
      let buckets' := buckets.update i .nil h
      ⟨size, buckets'.update i (bkt.replace a a) (by simpa [buckets'])⟩
    else
      let size'    := size + 1
      let buckets' := buckets.update i (a :: bkt) h
      if size' ≤ buckets.val.size
      then { size := size', buckets := buckets' }
      else expand size' buckets'

def erase [BEq α] [Hashable α] (m : HashSetImp α) (a : α) : HashSetImp α :=
  match m with
  | ⟨ size, buckets ⟩ =>
    let ⟨i, h⟩ := mkIdx (hash a) buckets.property
    let bkt    := buckets.val[i]
    if bkt.contains a then
      -- make sure `bkt` is used linearly in the following call to `erase`
      let buckets' := buckets.update i .nil h
      ⟨size - 1, buckets'.update i (bkt.erase a) (by simpa [buckets'])⟩
    else
      ⟨size, buckets⟩

inductive WellFormed [BEq α] [Hashable α] : HashSetImp α → Prop where
  | mkWff     : ∀ n,                  WellFormed (mkHashSetImp n)
  | insertWff : ∀ m a, WellFormed m → WellFormed (insert m a)
  | eraseWff  : ∀ m a, WellFormed m → WellFormed (erase m a)

end HashSetImp

def HashSet (α : Type u) [BEq α] [Hashable α] :=
  { m : HashSetImp α // m.WellFormed }

open HashSetImp

def mkHashSet {α : Type u} [BEq α] [Hashable α] (capacity := 8) : HashSet α :=
  ⟨ mkHashSetImp capacity, WellFormed.mkWff capacity ⟩

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

@[inline] def forM {m : Type w → Type w} [Monad m] (h : HashSet α) (f : α → m PUnit) : m PUnit :=
  match h with
  | ⟨h, _⟩ => h.forM f

instance : ForM m (HashSet α) α where
  forM := HashSet.forM

instance : ForIn m (HashSet α) α where
  forIn := ForM.forIn

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

/-- Insert many elements into a HashSet. -/
def insertMany [ForIn Id ρ α] (s : HashSet α) (as : ρ) : HashSet α := Id.run do
  let mut s := s
  for a in as do
    s := s.insert a
  return s

/--
`O(|t|)` amortized. Merge two `HashSet`s.
-/
@[inline]
def merge {α : Type u} [BEq α] [Hashable α] (s t : HashSet α) : HashSet α :=
  t.fold (init := s) fun s a => s.insert a
  -- We don't use `insertMany` here because it gives weird universes.

attribute [deprecated Std.HashSet (since := "2024-08-08")] HashSet
attribute [deprecated Std.HashSet.Raw (since := "2024-08-08")] HashSetImp
attribute [deprecated Std.HashSet.Raw.empty (since := "2024-08-08")] mkHashSetImp
attribute [deprecated Std.HashSet.empty (since := "2024-08-08")] mkHashSet
attribute [deprecated Std.HashSet.empty (since := "2024-08-08")] HashSet.empty
