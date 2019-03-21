/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.array.basic init.data.list.basic
import init.data.option.basic init.data.hashable
universes u v w

def bucketArray (α : Type u) (β : α → Type v) :=
{ b : Array (List (Σ a, β a)) // b.sz > 0 }

def bucketArray.uwrite {α : Type u} {β : α → Type v} (data : bucketArray α β) (i : USize) (d : List (Σ a, β a)) (h : i.toNat < data.val.sz) : bucketArray α β :=
⟨ data.val.uwrite i d h,
  transRelRight gt (Array.szWriteEq (data.val) ⟨USize.toNat i, h⟩ d) data.property ⟩

structure HashmapImp (α : Type u) (β : α → Type v) :=
(size       : Nat)
(buckets    : bucketArray α β)

def mkHashmapImp {α : Type u} {β : α → Type v} (nbuckets := 8) : HashmapImp α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
{ size       := 0,
  buckets    :=
  ⟨ mkArray n [],
    have p₁ : (mkArray n ([] : List (Σ a, β a))).sz = n, from szMkArrayEq _ _,
    have p₂ : n = (if nbuckets = 0 then 8 else nbuckets), from rfl,
    have p₃ : (if nbuckets = 0 then 8 else nbuckets) > 0, from
              match nbuckets with
              | 0            := Nat.zeroLtSucc _
              | (Nat.succ x) := Nat.zeroLtSucc _,
    transRelRight gt (Eq.trans p₁ p₂) p₃ ⟩ }

namespace HashmapImp
variables {α : Type u} {β : α → Type v}

def mkIdx {n : Nat} (h : n > 0) (u : USize) : { u : USize // u.toNat < n } :=
⟨u %ₙ n, USize.modnLt _ h⟩

def reinsertAux (hashFn : α → USize) (data : bucketArray α β) (a : α) (b : β a) : bucketArray α β :=
let ⟨i, h⟩ := mkIdx data.property (hashFn a) in
data.uwrite i (⟨a, b⟩ :: data.val.uread i h) h

def foldBuckets {δ : Type w} (data : bucketArray α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.val.foldl d (λ b d, b.foldl (λ r (p : Σ a, β a), f r p.1 p.2) d)

def findAux [DecidableEq α] (a : α) : List (Σ a, β a) → Option (β a)
| []          := none
| (⟨a',b⟩::t) :=
  if h : a' = a then some (Eq.recOn h b) else findAux t

def containsAux [DecidableEq α] (a : α) (l : List (Σ a, β a)) : Bool :=
(findAux a l).isSome

def find [DecidableEq α] [Hashable α] (m : HashmapImp α β) (a : α) : Option (β a) :=
match m with
| ⟨_, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a) in
  findAux a (buckets.val.uread i h)

def fold {δ : Type w} (m : HashmapImp α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
foldBuckets m.buckets d f

def replaceAux [DecidableEq α] (a : α) (b : β a) : List (Σ a, β a) → List (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replaceAux t

def eraseAux [DecidableEq α] (a : α) : List (Σ a, β a) → List (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: eraseAux t

def insert [DecidableEq α] [Hashable α] (m : HashmapImp α β) (a : α) (b : β a) : HashmapImp α β :=
match m with
| ⟨size, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a) in
  let bkt    := buckets.val.uread i h in
  if containsAux a bkt
  then ⟨size, buckets.uwrite i (replaceAux a b bkt) h⟩
  else let size'    := size + 1 in
       let buckets' := buckets.uwrite i (⟨a, b⟩::bkt) h in
       if size' <= buckets.val.sz
       then ⟨size', buckets'⟩
       else let nbuckets' := buckets.val.sz * 2 in
            let nz' : nbuckets' > 0 := Nat.mulPos buckets.property (Nat.zeroLtBit0 Nat.oneNeZero) in
            ⟨ size',
              foldBuckets buckets' ⟨mkArray nbuckets' [], nz'⟩ (reinsertAux hash) ⟩

def erase [DecidableEq α] [Hashable α] (m : HashmapImp α β) (a : α) : HashmapImp α β :=
match m with
| ⟨ size, buckets ⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a) in
  let bkt    := buckets.val.uread i h in
  if containsAux a bkt then ⟨size - 1, buckets.uwrite i (eraseAux a bkt) h⟩
  else m

inductive WellFormed [DecidableEq α] [Hashable α] : HashmapImp α β → Prop
| mkWff     : ∀ n,                     WellFormed (mkHashmapImp n)
| insertWff : ∀ m a b, WellFormed m → WellFormed (insert m a b)
| eraseWff  : ∀ m a,   WellFormed m → WellFormed (erase m a)

end HashmapImp

def DHashmap (α : Type u) (β : α → Type v) [DecidableEq α] [Hashable α] :=
{ m : HashmapImp α β // m.WellFormed }

open HashmapImp

def mkDHashmap {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α] (nbuckets := 8) : DHashmap α β :=
⟨ mkHashmapImp nbuckets, WellFormed.mkWff nbuckets ⟩

namespace DHashmap
variables {α : Type u} {β : α → Type v} [DecidableEq α] [Hashable α]

def insert (m : DHashmap α β) (a : α) (b : β a) : DHashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.insert a b, WellFormed.insertWff m a b hw ⟩

def erase (m : DHashmap α β) (a : α) : DHashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.erase a, WellFormed.eraseWff m a hw ⟩

def find (m : DHashmap α β) (a : α) : Option (β a) :=
match m with
| ⟨ m, _ ⟩ := m.find a

@[inline] def contains (m : DHashmap α β) (a : α) : Bool :=
(m.find a).isSome

def fold {δ : Type w} (m : DHashmap α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
match m with
| ⟨ m, _ ⟩ := m.fold d f

def size (m : DHashmap α β) : Nat :=
match m with
| ⟨ {size := sz, ..}, _ ⟩ := sz

@[inline] def empty (m : DHashmap α β) : Bool :=
m.size = 0

end DHashmap

def Hashmap (α : Type u) (β : Type v) [DecidableEq α] [Hashable α] :=
DHashmap α (λ _, β)

def mkHashmap {α : Type u} {β : Type v} [DecidableEq α] [Hashable α] (nbuckets := 8) : Hashmap α β  :=
mkDHashmap nbuckets

namespace Hashmap
variables {α : Type u} {β : Type v} [DecidableEq α] [Hashable α]

@[inline] def insert (m : Hashmap α β) (a : α) (b : β) : Hashmap α β :=
DHashmap.insert m a b

@[inline] def erase (m : Hashmap α β) (a : α) : Hashmap α β :=
DHashmap.erase m a

@[inline] def find (m : Hashmap α β) (a : α) : Option β :=
DHashmap.find m a

@[inline] def contains (m : Hashmap α β) (a : α) : Bool :=
(m.find a).isSome

@[inline] def fold {δ : Type w} (m : Hashmap α β) (d : δ) (f : δ → α → β → δ) : δ :=
DHashmap.fold m d f

@[inline] def size (m : Hashmap α β) : Nat :=
DHashmap.size m

@[inline] def empty (m : Hashmap α β) : Bool :=
DHashmap.empty m

end Hashmap
