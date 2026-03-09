variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α]
  {f : (a : α) → β a} {a : α} {b : β a}

/-- Replacing the value of a function at a given point by a given value. -/
def Function.update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=
  if h : a = a' then Eq.ndrec v h.symm else f a

@[simp]
theorem Function.update_self (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=
  dif_pos rfl

@[simp]
theorem Function.update_of_ne {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=
  dif_neg h

theorem domDomRestrict_aux {ι : Sort u_1} [DecidableEq ι] (P : ι → Prop) [DecidablePred P] {M₁ : ι → Type u_2}
    [DecidableEq {a // P a}]
    (x : (i : {a // P a}) → M₁ i) (z : (i : {a // ¬ P a}) → M₁ i) (i : {a : ι // P a})
    (c : M₁ i) : (fun j ↦ if h : P j then Function.update x i c ⟨j, h⟩ else z ⟨j, h⟩) =
    Function.update (fun j => if h : P j then x ⟨j, h⟩ else z ⟨j, h⟩) i c := by
  ext j
  by_cases h : j = i <;> grind only [Function.update_self, Function.update_of_ne]
