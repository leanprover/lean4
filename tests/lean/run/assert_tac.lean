import logic

variables {A : Type} {a a' : A}

definition to_eq₁ (H : a == a') : a = a' :=
begin
  assert H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a,
  intro Ht,
    exact (eq.refl (eq.rec_on Ht a)),
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end

definition to_eq₂ (H : a == a') : a = a' :=
begin
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a,
  begin
    intro Ht,
    exact (eq.refl (eq.rec_on Ht a))
  end,
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end

definition to_eq₃ (H : a == a') : a = a' :=
begin
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a,
  by intro Ht; exact (eq.refl (eq.rec_on Ht a)),
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end

definition to_eq₄ (H : a == a') : a = a' :=
begin
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a,
  from assume Ht, eq.refl (eq.rec_on Ht a),
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end

definition to_eq₅ (H : a == a') : a = a' :=
begin
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a,
  proof
    λ Ht, eq.refl (eq.rec_on Ht a)
  qed,
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end

definition to_eq₆ (H : a == a') : a = a' :=
begin
  have H₁ : ∀ (Ht : A = A), eq.rec_on Ht a = a, from
    assume Ht,
    eq.refl (eq.rec_on Ht a),
  show a = a', from
    heq.rec_on H H₁ (eq.refl A)
end
