import logic data.nat.basic
open nat

inductive inftree (A : Type) : Type :=
| leaf : A → inftree A
| node : (nat → inftree A) → inftree A → inftree A

namespace inftree
  inductive dsub {A : Type} : inftree A → inftree A → Prop :=
  | intro₁ : Π (f : nat → inftree A) (a : nat) (t : inftree A), dsub (f a) (node f t)
  | intro₂ : Π (f : nat → inftree A) (t : inftree A), dsub t (node f t)

  definition dsub.node.acc {A : Type} (f : nat → inftree A) (hf : ∀a, acc dsub (f a))
                                      (t : inftree A) (ht : acc dsub t) : acc dsub (node f t) :=
  acc.intro (node f t) (λ (y : inftree A) (hlt : dsub y (node f t)),
    begin
      cases hlt,
      apply (hf a),
      apply ht
    end)

end inftree
