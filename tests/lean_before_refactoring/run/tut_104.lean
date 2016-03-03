import data.set
namespace function
section
open set
variables {A B : Type}
set_option pp.beta false

lemma injective_eq_inj_on_univ₁ (f : A → B) : injective f = inj_on f univ :=
  begin
    esimp [injective, inj_on, univ, mem],
    apply propext,
    apply iff.intro,
      intro Pl a1 a2,
        rewrite *true_imp,
        exact @Pl a1 a2,
      intro Pr a1 a2,
      exact Pr trivial trivial
  end

lemma injective_eq_inj_on_univ₂ (f : A → B) : injective f = inj_on f univ :=
  begin
    esimp [injective, inj_on, univ, mem],
    apply propext,
    apply iff.intro,
      intro Pl a1 a2,
        rewrite *(propext !true_imp),
        exact @Pl a1 a2,
      intro Pr a1 a2,
      exact Pr trivial trivial
  end

lemma injective_eq_inj_on_univ₃ (f : A → B) : injective f = inj_on f univ :=
  begin
    esimp [injective, inj_on, univ, mem],
    apply propext,
    repeat (apply forall_congr; intros),
    rewrite *(propext !true_imp)
  end

lemma injective_eq_inj_on_univ₄ (f : A → B) : injective f = inj_on f univ :=
  begin
    esimp [injective, inj_on, univ, mem],
    apply propext,
    repeat (apply forall_congr; intros),
    rewrite *true_imp
  end
end

end function
