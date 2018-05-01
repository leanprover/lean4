/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.array.basic init.data.list.basic init.data.option.basic
universes u v w

def bucket_array (α : Type u) (β : α → Type v) (n : nat) :=
array n (list (Σ a, β a))

structure hashmap_imp (α : Type u) (β : α → Type v) :=
(size nbuckets : nat)
(nz_buckets    : nbuckets > 0)
(buckets       : bucket_array α β nbuckets)

def mk_hashmap_imp {α : Type u} {β : α → Type v} (nbuckets := 8) : hashmap_imp α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
{ size       := 0,
  nbuckets   := n,
  nz_buckets := show (if nbuckets = 0 then 8 else nbuckets) > 0, from
                match nbuckets with
                | 0            := nat.zero_lt_succ _
                | (nat.succ x) := nat.zero_lt_succ _
                end,
  buckets    := mk_array n [] }

namespace hashmap_imp
variables {α : Type u} {β : α → Type v}

def mk_idx {n : nat} (h : n > 0) (i : nat) : fin n :=
⟨i % n, nat.mod_lt _ h⟩

def reinsert_aux (hash_fn : α → nat) {n : nat} (h : n > 0) (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
let bidx := mk_idx h (hash_fn a) in
data.write bidx (⟨a, b⟩ :: data.read bidx)

def fold_buckets {δ : Type w} {n : nat} (data : bucket_array α β n) (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.foldl d (λ b d, b.foldl (λ r (p : Σ a, β a), f r p.1 p.2) d)

def find_aux [decidable_eq α] (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) :=
  if h : a' = a then some (eq.rec_on h b) else find_aux t

def contains_aux [decidable_eq α] (a : α) (l : list (Σ a, β a)) : bool :=
(find_aux a l).is_some

def find [decidable_eq α] (hash_fn : α → nat) (m : hashmap_imp α β) (a : α) : option (β a) :=
match m with
| ⟨_, nbuckets, nz, buckets⟩ :=
  find_aux a (buckets.read (mk_idx nz (hash_fn a)))
end

def fold {δ : Type w} (m : hashmap_imp α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
fold_buckets m.buckets d f

def replace_aux [decidable_eq α] (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

def erase_aux [decidable_eq α] (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

def insert [decidable_eq α] (hash_fn : α → nat) (m : hashmap_imp α β) (a : α) (b : β a) : hashmap_imp α β :=
match m with
| ⟨size, nbuckets, nz, buckets⟩ :=
  let bidx := mk_idx nz (hash_fn a) in
  let bkt  := buckets.read bidx in
  if contains_aux a bkt
  then ⟨size, nbuckets, nz, buckets.write bidx (replace_aux a b bkt)⟩
  else let size'    := size + 1 in
       let buckets' := buckets.write bidx (⟨a, b⟩::bkt) in
       if size' <= nbuckets
       then ⟨size', nbuckets, nz, buckets'⟩
       else let nbuckets' := nbuckets * 2 in
            let nz' : nbuckets' > 0 := nat.mul_pos nz (nat.zero_lt_bit0 nat.one_ne_zero) in
            ⟨size', nbuckets', nz',
            fold_buckets buckets' (mk_array nbuckets' []) $
               λ r a b, reinsert_aux hash_fn nz' r a b⟩
end

def erase [decidable_eq α] (hash_fn : α → nat) (m : hashmap_imp α β) (a : α) : hashmap_imp α β :=
match m with
| ⟨size, nbuckets, nz, buckets⟩ :=
  let bidx : fin nbuckets := ⟨hash_fn a % nbuckets, nat.mod_lt _ nz⟩ in
  let bkt                 := buckets.read bidx in
  if contains_aux a bkt
  then ⟨size - 1, nbuckets, nz, buckets.write bidx $ erase_aux a bkt⟩
  else m
end

inductive well_formed [decidable_eq α] (hash_fn : α → nat) : hashmap_imp α β → Prop
| mk_wff     : ∀ n,                     well_formed (mk_hashmap_imp n)
| insert_wff : ∀ m a b, well_formed m → well_formed (insert hash_fn m a b)
| erase_wff  : ∀ m a,   well_formed m → well_formed (erase hash_fn m a)

end hashmap_imp

def d_hashmap (α : Type u) (β : α → Type v) [decidable_eq α] (h : α → nat) :=
{ m : hashmap_imp α β // m.well_formed h }

open hashmap_imp

def mk_d_hashmap {α : Type u} {β : α → Type v} [decidable_eq α] (h : α → nat) (nbuckets := 8) : d_hashmap α β h :=
⟨ mk_hashmap_imp nbuckets, well_formed.mk_wff h nbuckets ⟩

namespace d_hashmap
variables {α : Type u} {β : α → Type v} [decidable_eq α] {h : α → nat}

def insert (m : d_hashmap α β h) (a : α) (b : β a) : d_hashmap α β h :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.insert h a b, well_formed.insert_wff m a b hw ⟩
end

def erase (m : d_hashmap α β h) (a : α) : d_hashmap α β h :=
match m with
| ⟨ m, hw ⟩ := ⟨ m.erase h a, well_formed.erase_wff m a hw ⟩
end

def find (m : d_hashmap α β h) (a : α) : option (β a) :=
match m with
| ⟨ m, _ ⟩ := m.find h a
end

@[inline] def contains (m : d_hashmap α β h) (a : α) : bool :=
(m.find a).is_some

def fold {δ : Type w} (m : d_hashmap α β h) (d : δ) (f : δ → Π a, β a → δ) : δ :=
match m with
| ⟨ m, _ ⟩ := m.fold d f
end

def size (m : d_hashmap α β h) : nat :=
match m with
| ⟨ {size := sz, ..}, _ ⟩ := sz
end

@[inline] def empty (m : d_hashmap α β h) : bool :=
m.size = 0

end d_hashmap

def hashmap (α : Type u) (β : Type v) [decidable_eq α] (h : α → nat) :=
d_hashmap α (λ _, β) h

def mk_hashmap {α : Type u} {β : Type v} [decidable_eq α] (h : α → nat) (nbuckets := 8) : hashmap α β h :=
mk_d_hashmap h nbuckets

namespace hashmap
variables {α : Type u} {β : Type v} [decidable_eq α] {h : α → nat}

@[inline] def insert (m : hashmap α β h) (a : α) (b : β) : hashmap α β h :=
d_hashmap.insert m a b

@[inline] def erase (m : hashmap α β h) (a : α) : hashmap α β h :=
d_hashmap.erase m a

@[inline] def contains (m : hashmap α β h) (a : α) : bool :=
(m.find a).is_some

@[inline] def fold {δ : Type w} (m : hashmap α β h) (d : δ) (f : δ → α → β → δ) : δ :=
d_hashmap.fold m d f

@[inline] def size (m : hashmap α β h) : nat :=
d_hashmap.size m

@[inline] def empty (m : hashmap α β h) : bool :=
d_hashmap.empty m

end hashmap
