/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.array.basic init.data.assoclist
import init.data.option.basic init.data.hashable
universes u v w

def HashMapBucket (α : Type u) (β : Type v) :=
{ b : Array (AssocList α β) // b.size > 0 }

def HashMapBucket.update {α : Type u} {β : Type v} (data : HashMapBucket α β) (i : USize) (d : AssocList α β) (h : i.toNat < data.val.size) : HashMapBucket α β :=
⟨ data.val.uset i d h,
  transRelRight Greater (Array.szFSetEq (data.val) ⟨USize.toNat i, h⟩ d) data.property ⟩

structure HashMapImp (α : Type u) (β : Type v) :=
(size       : Nat)
(buckets    : HashMapBucket α β)

def mkHashMapImp {α : Type u} {β : Type v} (nbuckets := 8) : HashMapImp α β :=
let n := if nbuckets = 0 then 8 else nbuckets;
{ size       := 0,
  buckets    :=
  ⟨ mkArray n AssocList.nil,
    have p₁ : (mkArray n (@AssocList.nil α β)).size = n, from Array.szMkArrayEq _ _,
    have p₂ : n = (if nbuckets = 0 then 8 else nbuckets), from rfl,
    have p₃ : (if nbuckets = 0 then 8 else nbuckets) > 0, from
              match nbuckets with
              | 0            := Nat.zeroLtSucc _
              | (Nat.succ x) := Nat.zeroLtSucc _,
    transRelRight Greater (Eq.trans p₁ p₂) p₃ ⟩ }

namespace HashMapImp
variables {α : Type u} {β : Type v}

def mkIdx {n : Nat} (h : n > 0) (u : USize) : { u : USize // u.toNat < n } :=
⟨u %ₙ n, USize.modnLt _ h⟩

@[inline] def reinsertAux (hashFn : α → USize) (data : HashMapBucket α β) (a : α) (b : β) : HashMapBucket α β :=
let ⟨i, h⟩ := mkIdx data.property (hashFn a);
data.update i (AssocList.cons a b (data.val.uget i h)) h

@[inline] def mfoldBuckets {δ : Type w} {m : Type w → Type w} [Monad m] (data : HashMapBucket α β) (d : δ) (f : δ → α → β → m δ) : m δ :=
data.val.mfoldl (fun d b => b.mfoldl f d) d

@[inline] def foldBuckets {δ : Type w} (data : HashMapBucket α β) (d : δ) (f : δ → α → β → δ) : δ :=
Id.run $ mfoldBuckets data d f

@[inline] def mfold {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → β → m δ) (d : δ) (h : HashMapImp α β) : m δ :=
mfoldBuckets h.buckets d f

@[inline] def fold {δ : Type w} (f : δ → α → β → δ) (d : δ) (m : HashMapImp α β) : δ :=
foldBuckets m.buckets d f

def find [HasBeq α] [Hashable α] (m : HashMapImp α β) (a : α) : Option β :=
match m with
| ⟨_, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a);
  (buckets.val.uget i h).find a

def contains [HasBeq α] [Hashable α] (m : HashMapImp α β) (a : α) : Bool :=
match m with
| ⟨_, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a);
  (buckets.val.uget i h).contains a

-- TODO: remove `partial` by using well-founded recursion
partial def moveEntries [Hashable α] : Nat → Array (AssocList α β) → HashMapBucket α β → HashMapBucket α β
| i source target :=
  if h : i < source.size then
     let idx : Fin source.size := ⟨i, h⟩;
     let es  : AssocList α β   := source.fget idx;
     -- We remove `es` from `source` to make sure we can reuse its memory cells when performing es.foldl
     let source                := source.fset idx AssocList.nil;
     let target                := es.foldl (reinsertAux hash) target;
     moveEntries (i+1) source target
  else target

def expand [Hashable α] (size : Nat) (buckets : HashMapBucket α β) : HashMapImp α β :=
let nbuckets := buckets.val.size * 2;
have aux₁  : nbuckets > 0, from Nat.mulPos buckets.property (Nat.zeroLtBit0 Nat.oneNeZero),
have aux₂  : (mkArray nbuckets (@AssocList.nil α β)).size = nbuckets, from Array.szMkArrayEq _ _,
let new_buckets : HashMapBucket α β := ⟨mkArray nbuckets AssocList.nil, aux₂.symm ▸ aux₁⟩;
{ size    := size,
  buckets := moveEntries 0 buckets.val new_buckets }

def insert [HasBeq α] [Hashable α] (m : HashMapImp α β) (a : α) (b : β) : HashMapImp α β :=
match m with
| ⟨size, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a);
  let bkt    := buckets.val.uget i h;
  if bkt.contains a
  then ⟨size, buckets.update i (bkt.replace a b) h⟩
  else
    let size'    := size + 1;
    let buckets' := buckets.update i (AssocList.cons a b bkt) h;
    if size' ≤ buckets.val.size
    then { size := size', buckets := buckets' }
    else expand size' buckets'

def erase [HasBeq α] [Hashable α] (m : HashMapImp α β) (a : α) : HashMapImp α β :=
match m with
| ⟨ size, buckets ⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a);
  let bkt    := buckets.val.uget i h;
  if bkt.contains a then ⟨size - 1, buckets.update i (bkt.erase a) h⟩
  else m

inductive WellFormed [HasBeq α] [Hashable α] : HashMapImp α β → Prop
| mkWff     : ∀ n,                    WellFormed (mkHashMapImp n)
| insertWff : ∀ m a b, WellFormed m → WellFormed (insert m a b)
| eraseWff  : ∀ m a,   WellFormed m → WellFormed (erase m a)

end HashMapImp

def HashMap (α : Type u) (β : Type v) [HasBeq α] [Hashable α] :=
{ m : HashMapImp α β // m.WellFormed }

open HashMapImp

def mkHashMap {α : Type u} {β : Type v} [HasBeq α] [Hashable α] (nbuckets := 8) : HashMap α β :=
⟨ mkHashMapImp nbuckets, WellFormed.mkWff nbuckets ⟩

namespace HashMap
variables {α : Type u} {β : Type v} [HasBeq α] [Hashable α]

instance : Inhabited (HashMap α β) :=
⟨mkHashMap⟩

instance : HasEmptyc (HashMap α β) :=
⟨mkHashMap⟩

@[inline] def insert (m : HashMap α β) (a : α) (b : β) : HashMap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.insert a b, WellFormed.insertWff m a b hw ⟩

@[inline] def erase (m : HashMap α β) (a : α) : HashMap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.erase a, WellFormed.eraseWff m a hw ⟩

@[inline] def find (m : HashMap α β) (a : α) : Option β :=
match m with
| ⟨ m, _ ⟩ := m.find a

@[inline] def contains (m : HashMap α β) (a : α) : Bool :=
match m with
| ⟨ m, _ ⟩ := m.contains a

@[inline] def mfold {δ : Type w} {m : Type w → Type w} [Monad m] (f : δ → α → β → m δ) (d : δ) (h : HashMap α β) : m δ :=
match h with
| ⟨ h, _ ⟩ := h.mfold f d

@[inline] def fold {δ : Type w} (f : δ → α → β → δ) (d : δ) (m : HashMap α β) : δ :=
match m with
| ⟨ m, _ ⟩ := m.fold f d

@[inline] def size (m : HashMap α β) : Nat :=
match m with
| ⟨ {size := sz, ..}, _ ⟩ := sz

@[inline] def empty (m : HashMap α β) : Bool :=
m.size = 0

def numBuckets (m : HashMap α β) : Nat :=
m.val.buckets.val.size

end HashMap
