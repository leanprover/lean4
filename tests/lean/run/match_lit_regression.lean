structure cmplx where
  X : Nat → Type
  d : ∀ i j, X i → X j
  shape : ∀ i j, ¬ i = j + 1 → d i j = sorry

def augment (C : cmplx) {X : Type} (f : C.X 0 → X) :
    cmplx where
  X | 0 => X
    | i + 1 => C.X i
  d | 1, 0 => f
    | i + 1, j + 1 => C.d i j
    | _, _ => sorry
  shape
    | 1, 0, h => absurd rfl h
    | i + 2, 0, _ => sorry
    | 0, _, _ => sorry
    | i + 1, j + 1, h => by simp; sorry
