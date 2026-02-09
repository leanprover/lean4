structure Equiv (α : Type _) (β : Type _) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x

def sumEquivSigmaBool (α β) : Equiv (α ⊕ β) (Σ b, bif b then β else α) where
  toFun s := s.elim (fun x => ⟨false, x⟩) fun x => ⟨true, x⟩
  invFun s :=
    match s with
    | ⟨false, a⟩ => .inl a
    | ⟨true, b⟩ => .inr b
  left_inv := fun s => by
    grind
