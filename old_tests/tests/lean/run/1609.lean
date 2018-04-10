universe variable u

inductive pred : ∀ (X : Type u), list X → Type (u+1)
| foo X (l1 : list X) (l2 : list (option X)) : pred (option X) l2 → pred X l1
