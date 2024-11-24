def myfunUnsafe (x : Array α) (i : Fin x.size) : Array α :=
  sorry

@[implemented_by myfunUnsafe]
def myfun (x : Array α) (i : Fin x.size) : Array α :=
  let next := 2*i.1 + 1
  if h : next < x.size then
      have : x.size - next < x.size - i.1 := sorry
      myfun (x.swap i next) ⟨next, (x.size_swap _ _).symm ▸ h⟩
  else
    x
termination_by x.size - i.1
