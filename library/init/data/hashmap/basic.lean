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
{ b : array (list (Σ a, β a)) // b.sz > 0 }

def bucketArray.uwrite {α : Type u} {β : α → Type v} (data : bucketArray α β) (i : usize) (d : list (Σ a, β a)) (h : i.toNat < data.val.sz) : bucketArray α β :=
⟨ data.val.uwrite i d h,
  transRelRight gt (array.szWriteEq (data.val) ⟨usize.toNat i, h⟩ d) data.property ⟩

structure hashmapImp (α : Type u) (β : α → Type v) :=
(size       : nat)
(buckets    : bucketArray α β)

def mkHashmapImp {α : Type u} {β : α → Type v} (nbuckets := 8) : hashmapImp α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
{ size       := 0,
  buckets    :=
  ⟨ mkArray n [],
    have p₁ : (mkArray n ([] : list (Σ a, β a))).sz = n, from szMkArrayEq _ _,
    have p₂ : n = (if nbuckets = 0 then 8 else nbuckets), from rfl,
    have p₃ : (if nbuckets = 0 then 8 else nbuckets) > 0, from
              match nbuckets with
              | 0            := nat.zeroLtSucc _
              | (nat.succ x) := nat.zeroLtSucc _,
    transRelRight gt (eq.trans p₁ p₂) p₃ ⟩ }

namespace hashmapImp
variables {α : Type u} {β : α → Type v}

def mkIdx {n : nat} (h : n > 0) (u : usize) : { u : usize // u.toNat < n } :=
⟨u %ₙ n, usize.modnLt _ h⟩

def reinsertAux (hashFn : α → usize) (data : bucketArray α β) (a : α) (b : β a) : bucketArray α β :=
let ⟨i, h⟩ := mkIdx data.property (hashFn a) in
data.uwrite i (⟨a, b⟩ :: data.val.uread i h) h

def foldBuckets {δ : Type w} (data : bucketArray α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.val.foldl d (λ b d, b.foldl (λ r (p : Σ a, β a), f r p.1 p.2) d)

def findAux [decidableEq α] (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) :=
  if h : a' = a then some (eq.recOn h b) else findAux t

def containsAux [decidableEq α] (a : α) (l : list (Σ a, β a)) : bool :=
(findAux a l).isSome

def find [decidableEq α] [hashable α] (m : hashmapImp α β) (a : α) : option (β a) :=
match m with
| ⟨_, buckets⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a) in
  findAux a (buckets.val.uread i h)

def fold {δ : Type w} (m : hashmapImp α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
foldBuckets m.buckets d f

def replaceAux [decidableEq α] (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replaceAux t

def eraseAux [decidableEq α] (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: eraseAux t

def insert [decidableEq α] [hashable α] (m : hashmapImp α β) (a : α) (b : β a) : hashmapImp α β :=
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
            let nz' : nbuckets' > 0 := nat.mulPos buckets.property (nat.zeroLtBit0 nat.oneNeZero) in
            ⟨ size',
              foldBuckets buckets' ⟨mkArray nbuckets' [], nz'⟩ (reinsertAux hash) ⟩

def erase [decidableEq α] [hashable α] (m : hashmapImp α β) (a : α) : hashmapImp α β :=
match m with
| ⟨ size, buckets ⟩ :=
  let ⟨i, h⟩ := mkIdx buckets.property (hash a) in
  let bkt    := buckets.val.uread i h in
  if containsAux a bkt then ⟨size - 1, buckets.uwrite i (eraseAux a bkt) h⟩
  else m

inductive wellFormed [decidableEq α] [hashable α] : hashmapImp α β → Prop
| mkWff     : ∀ n,                     wellFormed (mkHashmapImp n)
| insertWff : ∀ m a b, wellFormed m → wellFormed (insert m a b)
| eraseWff  : ∀ m a,   wellFormed m → wellFormed (erase m a)

end hashmapImp

def dHashmap (α : Type u) (β : α → Type v) [decidableEq α] [hashable α] :=
{ m : hashmapImp α β // m.wellFormed }

open hashmapImp

def mkDHashmap {α : Type u} {β : α → Type v} [decidableEq α] [hashable α] (nbuckets := 8) : dHashmap α β :=
⟨ mkHashmapImp nbuckets, wellFormed.mkWff nbuckets ⟩

namespace dHashmap
variables {α : Type u} {β : α → Type v} [decidableEq α] [hashable α]

def insert (m : dHashmap α β) (a : α) (b : β a) : dHashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.insert a b, wellFormed.insertWff m a b hw ⟩

def erase (m : dHashmap α β) (a : α) : dHashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.erase a, wellFormed.eraseWff m a hw ⟩

def find (m : dHashmap α β) (a : α) : option (β a) :=
match m with
| ⟨ m, _ ⟩ := m.find a

@[inline] def contains (m : dHashmap α β) (a : α) : bool :=
(m.find a).isSome

def fold {δ : Type w} (m : dHashmap α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
match m with
| ⟨ m, _ ⟩ := m.fold d f

def size (m : dHashmap α β) : nat :=
match m with
| ⟨ {size := sz, ..}, _ ⟩ := sz

@[inline] def empty (m : dHashmap α β) : bool :=
m.size = 0

end dHashmap

def hashmap (α : Type u) (β : Type v) [decidableEq α] [hashable α] :=
dHashmap α (λ _, β)

def mkHashmap {α : Type u} {β : Type v} [decidableEq α] [hashable α] (nbuckets := 8) : hashmap α β  :=
mkDHashmap nbuckets

namespace hashmap
variables {α : Type u} {β : Type v} [decidableEq α] [hashable α]

@[inline] def insert (m : hashmap α β) (a : α) (b : β) : hashmap α β :=
dHashmap.insert m a b

@[inline] def erase (m : hashmap α β) (a : α) : hashmap α β :=
dHashmap.erase m a

@[inline] def find (m : hashmap α β) (a : α) : option β :=
dHashmap.find m a

@[inline] def contains (m : hashmap α β) (a : α) : bool :=
(m.find a).isSome

@[inline] def fold {δ : Type w} (m : hashmap α β) (d : δ) (f : δ → α → β → δ) : δ :=
dHashmap.fold m d f

@[inline] def size (m : hashmap α β) : nat :=
dHashmap.size m

@[inline] def empty (m : hashmap α β) : bool :=
dHashmap.empty m

end hashmap
