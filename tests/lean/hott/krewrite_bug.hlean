import algebra.category.functor

open function category eq prod prod.ops equiv is_equiv sigma sigma.ops is_trunc funext iso
open pi

namespace functor
  variables {A B C D E : Precategory}

  definition compose_pentagon_test (K : D ⇒ E) (H : C ⇒ D) (G : B ⇒ C) (F : A ⇒ B) :
    (calc K ∘f H ∘f G ∘f F = (K ∘f H) ∘f G ∘f F : functor.assoc
      ... = ((K ∘f H) ∘f G) ∘f F : functor.assoc)
    =
    (calc K ∘f H ∘f G ∘f F = K ∘f (H ∘f G) ∘f F : ap (λx, K ∘f x) !functor.assoc
      ... = (K ∘f H ∘f G) ∘f F : functor.assoc
      ... = ((K ∘f H) ∘f G) ∘f F : ap (λx, x ∘f F) !functor.assoc) :=
  begin
  have lem1  : Π{F₁ F₂ : A ⇒ D} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (λx, K ∘f x) p) a = ap (to_fun_ob K) (ap010 to_fun_ob p a),
      by intros; cases p; esimp,
  have lem2 : Π{F₁ F₂ : B ⇒ E} (p : F₁ = F₂) (a : A),
    ap010 to_fun_ob (ap (λx, x ∘f F) p) a = ap010 to_fun_ob p (F a),
      by intros; cases p; esimp,
  apply functor_eq2,
  intro a, esimp,
  krewrite [ap010_con],
  rewrite [+ap010_con,lem1,lem2,
          ap010_assoc K H (G ∘f F) a,
          ap010_assoc (K ∘f H) G F a,
          ap010_assoc H G F a,
          ap010_assoc K H G (F a),
          ap010_assoc K (H ∘f G) F a]
  end

end functor
