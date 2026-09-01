theorem Nat.lt_of_lt_le {x y z : Nat} : x < y → y ≤ z → x < z := by
  intro h h'
  induction h'
  assumption
  apply Nat.le_step
  assumption

structure ArrayBuffer (α) where
  cap : Nat
  backing : Fin cap → Option α
  size : Nat
  h_size : size ≤ cap
  h_full : ∀ i, (h:i < size) → (backing ⟨i, Nat.lt_of_lt_le h h_size⟩).isSome

namespace ArrayBuffer

def grow : ArrayBuffer α → ArrayBuffer α :=
λ ⟨cap, backing, size, h_size, h_full⟩ =>
  ⟨cap + cap,
    λ i => if h:i < cap then backing ⟨i,h⟩ else none,
    size,
    Nat.le_trans h_size (Nat.le_add_left _ _),
    by intro i h
       simp
       trace_state
       have : i < cap := Nat.lt_of_lt_le h h_size
       simp [*]⟩
