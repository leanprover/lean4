/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
universes u v w

def bucket_array (α : Type u) (β : α → Type v) (n : nat) :=
array (list (Σ a, β a)) n

structure hash_map (α : Type u) [decidable_eq α] (β : α → Type v) :=
(hash_fn : α → nat)
(size nbuckets : nat)
(nz_buckets : nbuckets > 0)
(buckets : bucket_array α β nbuckets)

def mk_hash_map {α : Type u} [decidable_eq α] {β : α → Type v} (hash_fn : α → nat) (nbuckets := 8) : hash_map α β :=
let n := if nbuckets = 0 then 8 else nbuckets in
{hash_fn    := hash_fn,
 size       := 0,
 nbuckets   := n,
 nz_buckets := by abstract {dsimp, cases nbuckets, {simp, tactic.comp_val}, simp [if_pos, nat.succ_ne_zero], apply nat.zero_lt_succ},
 buckets    := mk_array n [] }

namespace hash_map
variables {α : Type u} {β : α → Type v} {δ : Type w}

def mk_idx {n : nat} (h : n > 0) (i : nat) : fin n :=
⟨i % n, nat.mod_lt _ h⟩

def reinsert_aux (hash_fn : α → nat) {n : nat} (h : n > 0) (data : bucket_array α β n) (a : α) (b : β a) : bucket_array α β n :=
let bidx := mk_idx h (hash_fn a) in
data.write bidx (⟨a, b⟩ :: data.read bidx)

def fold_buckets {n : nat} (data : bucket_array α β n) (d : δ) (f : δ → Π a, β a → δ) : δ :=
data.foldl d (λ b d, b.foldl (λ r (p : Σ a, β a), f r p.1 p.2) d)

variable [decidable_eq α]

def find_aux (a : α) : list (Σ a, β a) → option (β a)
| []          := none
| (⟨a',b⟩::t) :=
  if h : a' = a then some (eq.rec_on h b) else find_aux t

def contains_aux (a : α) (l : list (Σ a, β a)) : bool :=
(find_aux a l)^.is_some

def find (m : hash_map α β) (a : α) : option (β a) :=
match m with
| ⟨hash_fn, _, nbuckets, nz, buckets⟩ :=
  find_aux a (buckets.read (mk_idx nz (hash_fn a)))
end

def contains (m : hash_map α β) (a : α) : bool :=
(find m a)^.is_some

def fold [decidable_eq α] (m : hash_map α β) (d : δ) (f : δ → Π a, β a → δ) : δ :=
fold_buckets m.buckets d f

def replace_aux (a : α) (b : β a) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then ⟨a, b⟩::t else ⟨a', b'⟩ :: replace_aux t

def erase_aux (a : α) : list (Σ a, β a) → list (Σ a, β a)
| []            := []
| (⟨a', b'⟩::t) := if a' = a then t else ⟨a', b'⟩ :: erase_aux t

def insert (m : hash_map α β) (a : α) (b : β a) : hash_map α β :=
match m with
| ⟨hash_fn, size, nbuckets, nz, buckets⟩ :=
  let bidx := mk_idx nz (hash_fn a) in
  let bkt  := buckets.read bidx in
  if contains_aux a bkt
  then ⟨hash_fn, size, nbuckets, nz, buckets.write bidx (replace_aux a b bkt)⟩
  else let size'    := size + 1 in
       let buckets' := buckets.write bidx (⟨a, b⟩::bkt) in
       if size' <= nbuckets
       then ⟨hash_fn, size', nbuckets, nz, buckets'⟩
       else let nbuckets' := nbuckets * 2 in
            let nz' : nbuckets' > 0 := mul_pos nz dec_trivial in
            ⟨hash_fn, size', nbuckets', nz',
            fold_buckets buckets' (mk_array nbuckets' []) $
               λ r a b, reinsert_aux hash_fn nz' r a b⟩
end

def erase (m : hash_map α β) (a : α) : hash_map α β :=
match m with
| ⟨hash_fn, size, nbuckets, nz, buckets⟩ :=
  let bidx : fin nbuckets := ⟨hash_fn a % nbuckets, nat.mod_lt _ nz⟩ in
  let bkt                 := buckets.read bidx in
  if contains_aux a bkt
  then ⟨hash_fn, size - 1, nbuckets, nz, buckets.write bidx $ erase_aux a bkt⟩
  else m
end

section string
variables [has_to_string α] [∀ a, has_to_string (β a)]
open prod
private def key_data_to_string (a : α) (b : β a) (first : bool) : string :=
(if first then "" else ", ") ++ to_string a ++ " ← " ++ to_string b

private def to_string (m : hash_map α β) : string :=
"⟨" ++ (fst (fold m ("", tt) (λ p a b, (fst p ++ key_data_to_string a b (snd p), ff)))) ++ "⟩"

instance : has_to_string (hash_map α β) :=
⟨to_string⟩

end string

section format
open format prod
variables [has_to_format α] [∀ a, has_to_format (β a)]

private meta def format_key_data (a : α) (b : β a) (first : bool) : format :=
(if first then to_fmt "" else to_fmt "," ++ line) ++ to_fmt a ++ space ++ to_fmt "←" ++ space ++ to_fmt b

private meta def to_format (m : hash_map α β) : format :=
group $ to_fmt "⟨" ++ nest 1 (fst (fold m (to_fmt "", tt) (λ p a b, (fst p ++ format_key_data a b (snd p), ff)))) ++
        to_fmt "⟩"

meta instance : has_to_format (hash_map α β) :=
⟨to_format⟩
end format
end hash_map
