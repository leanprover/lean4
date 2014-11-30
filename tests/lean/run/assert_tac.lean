import logic

variables {A : Type} {a a' : A}

definition to_eq (H : a == a') : a = a' :=
begin
  assert (H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a),
  intro Ht,
    exact (eq.refl (eq.rec_on Ht a)),
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end
