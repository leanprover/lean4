open eq is_trunc

structure is_retraction [class] {A B : Type} (f : A → B) :=
  (sect : B → A)
  (right_inverse : Π(b : B), f (sect b) = b)

definition foo
{A : Type}
{B : Type}
(f : A → B)
(g : B → A)
(ε : Πb, f (g b) = b)
(b b' : B)
  : is_retraction (λ (q : g b = g b'), (ε b) ⁻¹ ⬝ ap f q ⬝ ε b') :=
begin
  fapply is_retraction.mk,
    {exact (@ap B A g b b') },
    {intro p, cases p, esimp [eq.ap, eq.rec_on, eq.idp] }
end
