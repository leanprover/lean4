namespace Ex1
  variable (a : Nat) (i : Fin a) (h : 1 = a)
  example : i < a := h ▸ i.2 -- `▸` uses `subst` here
end Ex1

namespace Ex2
def heapifyDown' (a : Array α) (i : Fin a.size) : Array α := sorry
def heapifyDown (a : Array α) (i : Fin a.size) : Array α :=
  heapifyDown' a ⟨i.1, a.size_swap i i ▸ i.2⟩ -- Error, failed to compute motive, `subst` is not applicable here
end Ex2

namespace Ex3
def heapifyDown (a : Array α) (i : Fin a.size) : Array α :=
  have : i < i := sorry
  heapifyDown a ⟨i.1, a.size_swap i i ▸ i.2⟩ -- Error, failed to compute motive, `subst` is not applicable here
termination_by i.1
decreasing_by assumption
end Ex3

namespace Ex4
def heapifyDown (lt : α → α → Bool) (a : Array α) (i : Fin a.size) : Array α :=
  let left := 2 * i.1 + 1
  let right := left + 1
  have left_le : i ≤ left := sorry
  have right_le : i ≤ right := sorry
  have i_le : i ≤ i := Nat.le_refl _
  have j : {j : Fin a.size // i ≤ j} := if h : left < a.size then
    if lt a[i] a[left] then ⟨⟨left, h⟩, left_le⟩ else ⟨i, i_le⟩ else ⟨i, i_le⟩
  have j := if h : right < a.size then
    if lt a[j.1.1] a[right] then ⟨⟨right, h⟩, right_le⟩ else j else j
  if h : i ≠ j then
    let a' := a.swap i j
    have : a'.size - j < a.size - i := sorry
    heapifyDown lt a' ⟨j.1.1, a.size_swap i j ▸ j.1.2⟩ -- Error, failed to compute motive, `subst` is not applicable here
  else
    a
termination_by a.size - i.1
decreasing_by assumption
end Ex4
