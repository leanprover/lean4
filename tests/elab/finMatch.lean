variable (F : Fin 4 → Type) (a : F 0 → F 1) (b : F 1 → F 2) (c : F 2 → F 3)

def map : (i j : Fin 4) → (hij : i ≤ j) → F i → F j
  | 0, 0, _ => id
  | 1, 1, _ => id
  | 2, 2, _ => id
  | 3, 3, _ => id
  | 0, 1, _ => a
  | 0, 2, _ => b ∘ a
  | 0, 3, _ => c ∘ b ∘ a
  | 1, 2, _ => b
  | 1, 3, _ => c ∘ b
  | 2, 3, _ => c
