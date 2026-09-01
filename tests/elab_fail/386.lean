class Fintype (α : Type) where
axiom Finset (α : Type) : Type
axiom Finset.univ {α : Type} [Fintype α] : Finset α
axiom Finset.filter {α : Type} (s : Finset α) (ϕ : α → Bool) : Finset α

-- The following should not elaborate, since there are no `Fintype` instances
-- Instead it yields: "error: (kernel) declaration has metavariables 'kernelErrorMetavar'"
def kernelErrorMetavar1 (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun (i : Fin n) => true)

instance : Fintype (Fin n) := ⟨⟩

noncomputable def kernelErrorMetavar2 (n : Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun (i : Fin n) => true)
