namespace n1
def f : {n : ℕ // n = 0} → {n : ℕ // n = 0}
| ⟨ v, h ⟩ := ⟨ v, h.symm.symm ⟩

def g : {n : ℕ // n = 0} → {n : ℕ // n = 0} :=
λ x, subtype.cases_on x (λ v h, ⟨v, h.symm.symm⟩)
end n1

#check @n1.f._main._proof_1
#check @n1.g._proof_1
