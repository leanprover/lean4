/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.array.basic init.data.list.basic
import init.data.option.basic init.data.hashable
universes u v w

def bucket_array (α : Type u) (β : α → Type v) :=
{ b : array (list (Σ a, β a)) // b.sz > 0 }

def bucket_array.uwrite {α : Type u} {β : α → Type v} (data : bucket_array α β) (i : usize) (d : list (Σ a, β a)) (h : i.to_nat < data.val.sz) : bucket_array α β :=
⟨ data.val.uwrite i d h,
  trans_rel_right gt (array.sz_write_eq (data.val) ⟨usize.to_nat i, h⟩ d) data.property ⟩

structure hashmap_imp (α : Type u) (β : α → Type v) :=
(size       : nat)
(buckets    : bucket_array α β)

def mk_hashmap_imp {α : Type u} {β : α → Type v} (nbuckets := 8) : hashmap_imp α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
{ size       := 0,
  buckets    :=
  ⟨ mk_array n [],
    have p₁ : (mk_array n []).sz = n, from sz_mk_array_eq _ _,
    have p₂ : n = (if nbuckets = 0 then 8 else nbuckets), from rfl,
    have p₃ : (if nbuckets = 0 then 8 else nbuckets) > 0, from
              match nbuckets with
              | 0            := nat.zero_lt_succ _
              | (nat.succ x) := nat.zero_lt_succ _,
    trans_rel_right gt (eq.trans p₁ p₂) p₃ ⟩ }

namespace hashmap_imp
variables {α : Type u} {β : α → Type v}

def mk_idx {n : nat} (h : n > 0) (u : usize) : { u : usize // u.to_nat < n } :=
⟨u %ₙ n, usize.modn_lt _ h⟩

def reinsert_aux (hash_fn : α → usize) (data : bucket_array α β) (a : α) (b : β a) : bucket_array α β :=
let ⟨i, h⟩ := mk_idx data.property (hash_fn a) in
data.uwrite i (⟨a, b⟩ :: data.val.uread i h) h

def fold_buckets {δ : Type w} (data : bucket_array α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.val.foldl d (λ b d, b.foldl (λ r (p : Σ a, β a), f r p.1 p.2) d)

def find_aux [decidable_eq α] (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) :=
  if h : a' = a then some (eq.rec_on h b) else find_aux t

def contains_aux [decidable_eq α] (a : α) (l : list (Σ a, β a)) : bool :=
(find_aux a l).is_some

def find [decidable_eq α] [hashable α] (m : hashmap_imp α β) (a : α) : option (β a) :=
match m with
| ⟨_, buckets⟩ :=
  let ⟨i, h⟩ := mk_idx buckets.property (hash a) in
  find_aux a (buckets.val.uread i h)

def fold {δ : Type w} (m : hashmap_imp α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
fold_buckets m.buckets d f

def replace_aux [decidable_eq α] (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

def erase_aux [decidable_eq α] (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

def insert [decidable_eq α] [hashable α] (m : hashmap_imp α β) (a : α) (b : β a) : hashmap_imp α β :=
match m with
| ⟨size, buckets⟩ :=
  let ⟨i, h⟩ := mk_idx buckets.property (hash a) in
  let bkt    := buckets.val.uread i h in
  if contains_aux a bkt
  then ⟨size, buckets.uwrite i (replace_aux a b bkt) h⟩
  else let size'    := size + 1 in
       let buckets' := buckets.uwrite i (⟨a, b⟩::bkt) h in
       if size' <= buckets.val.sz
       then ⟨size', buckets'⟩
       else let nbuckets' := buckets.val.sz * 2 in
            let nz' : nbuckets' > 0 := nat.mul_pos buckets.property (nat.zero_lt_bit0 nat.one_ne_zero) in
            ⟨ size',
              fold_buckets buckets' ⟨mk_array nbuckets' [], nz'⟩ (reinsert_aux hash) ⟩

def erase [decidable_eq α] [hashable α] (m : hashmap_imp α β) (a : α) : hashmap_imp α β :=
match m with
| ⟨ size, buckets ⟩ :=
  let ⟨i, h⟩ := mk_idx buckets.property (hash a) in
  let bkt    := buckets.val.uread i h in
  if contains_aux a bkt then ⟨size - 1, buckets.uwrite i (erase_aux a bkt) h⟩
  else m

inductive well_formed [decidable_eq α] [hashable α] : hashmap_imp α β → Prop
| mk_wff     : ∀ n,                     well_formed (mk_hashmap_imp n)
| insert_wff : ∀ m a b, well_formed m → well_formed (insert m a b)
| erase_wff  : ∀ m a,   well_formed m → well_formed (erase m a)

end hashmap_imp

def d_hashmap (α : Type u) (β : α → Type v) [decidable_eq α] [hashable α] :=
{ m : hashmap_imp α β // m.well_formed }

open hashmap_imp

def mk_d_hashmap {α : Type u} {β : α → Type v} [decidable_eq α] [hashable α] (nbuckets := 8) : d_hashmap α β :=
⟨ mk_hashmap_imp nbuckets, well_formed.mk_wff nbuckets ⟩

namespace d_hashmap
variables {α : Type u} {β : α → Type v} [decidable_eq α] [hashable α]

def insert (m : d_hashmap α β) (a : α) (b : β a) : d_hashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.insert a b, well_formed.insert_wff m a b hw ⟩

def erase (m : d_hashmap α β) (a : α) : d_hashmap α β :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.erase a, well_formed.erase_wff m a hw ⟩

def find (m : d_hashmap α β) (a : α) : option (β a) :=
match m with
| ⟨ m, _ ⟩ := m.find a

@[inline] def contains (m : d_hashmap α β) (a : α) : bool :=
(m.find a).is_some

def fold {δ : Type w} (m : d_hashmap α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
match m with
| ⟨ m, _ ⟩ := m.fold d f

def size (m : d_hashmap α β) : nat :=
match m with
| ⟨ {size := sz, ..}, _ ⟩ := sz

@[inline] def empty (m : d_hashmap α β) : bool :=
m.size = 0

end d_hashmap

def hashmap (α : Type u) (β : Type v) [decidable_eq α] [hashable α] :=
d_hashmap α (λ _, β)

def mk_hashmap {α : Type u} {β : Type v} [decidable_eq α] [hashable α] (nbuckets := 8) : hashmap α β  :=
mk_d_hashmap nbuckets

namespace hashmap
variables {α : Type u} {β : Type v} [decidable_eq α] [hashable α]

@[inline] def insert (m : hashmap α β) (a : α) (b : β) : hashmap α β :=
d_hashmap.insert m a b

@[inline] def erase (m : hashmap α β) (a : α) : hashmap α β :=
d_hashmap.erase m a

@[inline] def find (m : hashmap α β) (a : α) : option β :=
d_hashmap.find m a

@[inline] def contains (m : hashmap α β) (a : α) : bool :=
(m.find a).is_some

@[inline] def fold {δ : Type w} (m : hashmap α β) (d : δ) (f : δ → α → β → δ) : δ :=
d_hashmap.fold m d f

@[inline] def size (m : hashmap α β) : nat :=
d_hashmap.size m

@[inline] def empty (m : hashmap α β) : bool :=
d_hashmap.empty m

end hashmap
