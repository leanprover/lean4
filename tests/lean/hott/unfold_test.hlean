import algebra.e_closure

open eq

namespace relation
section
  parameters {A : Type}
             (R : A → A → Type)

  local abbreviation T := e_closure R

  variables ⦃a a' : A⦄ {s : R a a'} {r : T a a}
  parameter {R}

  theorem ap_ap_e_closure_elim_h₁ {B C D : Type} {f : A → B}
    {g : B → C} (h : C → D)
    (e : Π⦃a a' : A⦄, R a a' → f a = f a')
    {e' : Π⦃a a' : A⦄, R a a' → g (f a) = g (f a')}
    (p : Π⦃a a' : A⦄ (s : R a a'), ap g (e s) = e' s) (t : T a a')
    : square (ap (ap h) (ap_e_closure_elim_h e p t))
             (ap_e_closure_elim_h e (λa a' s, ap_compose h g (e s)) t)
             (ap_compose h g (e_closure.elim e t))⁻¹
             (ap_e_closure_elim_h e' (λa a' s, (ap (ap h) (p s))⁻¹) t) :=
  begin
    induction t,
    apply sorry,
    apply sorry,
    {
      rewrite [↑e_closure.elim, ↑ap_e_closure_elim_h, ap_con (ap h)],
      refine (transpose !ap_compose_inv)⁻¹ᵛ ⬝h _,
      rewrite [con_inv,inv_inv,-inv2_inv],
      exact !ap_inv2 ⬝v square_inv2 v_0
     },
    apply sorry
  end
end
end relation
