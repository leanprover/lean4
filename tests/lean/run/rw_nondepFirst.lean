def Set (ι : Type) := ι → Prop

namespace Set

def univ : Set ι := fun _ => True
def empty : Set ι := fun _ => False

def pi {ι : Type} {α : ι → Type} (s : Set ι) (t : (i : ι) → Set (α i)) : Set ((i : ι) → α i) := sorry

theorem univ_pi_eq_empty (ht : t i = empty) : Set.pi univ t = empty := sorry

example (i : ι) (h : t i = empty) : Set.pi univ t = empty := by
  rw [univ_pi_eq_empty]
  · exact h
