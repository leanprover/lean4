inductive formula :=
| eqf  : nat → nat → formula
| andf : formula → formula → formula
| impf : formula → formula → formula
| notf : formula → formula
| orf  : formula → formula → formula
| allf : (nat → formula) → formula

namespace formula
  definition implies (a b : Prop) : Prop := a → b

  definition denote : formula → Prop
  | denote (eqf n1 n2)  := n1 = n2
  | denote (andf f1 f2) := denote f1 ∧ denote f2
  | denote (impf f1 f2) := implies (denote f1) (denote f2)
  | denote (orf f1 f2)  := denote f1 ∨ denote f2
  | denote (notf f)     := ¬ denote f
  | denote (allf f)     := ∀ n : nat, denote (f n)

  theorem denote_eqf (n1 n2 : nat) : denote (eqf n1 n2) = (n1 = n2) :=
  rfl

  theorem denote_andf (f1 f2 : formula) : denote (andf f1 f2) = (denote f1 ∧ denote f2) :=
  rfl

  theorem denote_impf (f1 f2 : formula) : denote (impf f1 f2) = (denote f1 → denote f2) :=
  rfl

  theorem denote_orf (f1 f2 : formula) : denote (orf f1 f2) = (denote f1 ∨ denote f2) :=
  rfl

  theorem denote_notf (f : formula) : denote (notf f) = ¬ denote f :=
  rfl

  theorem denote_allf (f : nat → formula) : denote (allf f) = (∀ n, denote (f n)) :=
  rfl

  example : denote (allf (λ n₁, allf (λ n₂, impf (eqf n₁ n₂) (eqf n₂ n₁)))) =
            (∀ n₁ n₂ : nat, n₁ = n₂ → n₂ = n₁) :=
  rfl

end formula
