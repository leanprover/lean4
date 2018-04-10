inductive formula :=
eqf : nat → nat → formula,
andf : formula → formula → formula,
impf : formula → formula → formula,
allf : (nat → formula) → formula

check @formula.rec_on

namespace formula

  definition denote : formula → Prop,
  denote (eqf n1 n2)  := n1 = n2,
  denote (andf f1 f2) := denote f1 ∧ denote f2,
  denote (impf f1 f2) := denote f1 → denote f2,
  denote (allf f)     := ∀ n : nat, denote (f n)

end formula

definition denote (f : formula) : Prop :=
formula.rec_on f
  (λ n₁ n₂, n₁ = n₂)
  (λ f₁ f₂ r₁ r₂, r₁ ∧ r₂)
  (λ f₁ f₂ r₁ r₂, r₁ → r₂)
  (λ f r, ∀ n : nat, r n)

open formula
eval denote (allf (λ n₁, allf (λ n₂, impf (eqf n₁ n₂) (eqf n₂ n₁))))
