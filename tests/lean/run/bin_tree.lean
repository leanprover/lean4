def pairs_with_sum' : Π (m n) {d}, m + n = d → list {p : ℕ × ℕ // p.1 + p.2 = d}
| 0     n d h := [⟨(0, n), h⟩]
| (m+1) n d h := ⟨(m+1, n), h⟩ :: pairs_with_sum' m (n+1) (by simp at h; simp [h])

def pairs_with_sum (n) : list {p : ℕ × ℕ // p.1 + p.2 = n} :=
pairs_with_sum' n 0 rfl

inductive bin_tree
| leaf : bin_tree
| branch : bin_tree → bin_tree → bin_tree
open bin_tree

def size : bin_tree → ℕ
| leaf := 0
| (branch l r) := size l + size r + 1

def trees_of_size : Π s, list {bt : bin_tree // size bt = s}
| 0     := [⟨leaf, rfl⟩]
| (n+1) :=
  do ⟨(s1, s2), (h : s1 + s2 = n)⟩ ← pairs_with_sum n,
     ⟨t1, sz1⟩ ← have s1 < n+1, by apply nat.lt_succ_of_le; rw ←h; apply nat.le_add_right,
                trees_of_size s1,
     ⟨t2, sz2⟩ ← have s2 < n+1, by apply nat.lt_succ_of_le; rw ←h; apply nat.le_add_left,
                trees_of_size s2,
     return ⟨branch t1 t2, by rw [←h, ←sz1, ←sz2]; refl⟩
