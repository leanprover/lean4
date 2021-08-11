instance (ϕ : α → Prop) : CoeSort (Subtype ϕ) α where
  coe := fun x => x.val

example (ϕ : α → Prop) (xs : Subtype ϕ) (x : xs) : True := trivial
