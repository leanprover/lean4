import data.hash_map

open hash_map

universes u v w
section
parameters {α : Type u} {β : α → Type v} (hash_fn : α → nat)
parameter [decidable_eq α]

attribute [congr] dif_ctx_simp_congr
attribute [congr] if_ctx_simp_congr

theorem mem_insert' : Π (m : hash_map α β) (a b a' b'),
  sigma.mk a' b' ∈ (m.insert a b).entries ↔
  if a = a' then b == b' else sigma.mk a' b' ∈ m.entries
| ⟨hash_fn, size, n, bkts, v⟩ a b a' b' :=
by simp[hash_map.insert]; exact sorry

end
