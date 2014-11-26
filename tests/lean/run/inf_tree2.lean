import logic data.nat.basic
open nat

inductive inftree (A : Type) : Type :=
leaf : A → inftree A,
node : (nat → inftree A) → inftree A → inftree A

namespace inftree
  inductive dsub {A : Type} : inftree A → inftree A → Prop :=
  intro₁ : Π (f : nat → inftree A) (a : nat) (t : inftree A), dsub (f a) (node f t),
  intro₂ : Π (f : nat → inftree A) (a : nat) (t : inftree A), dsub t (node f t)

  definition dsub.node.acc {A : Type} (f : nat → inftree A) (hf : ∀a, acc dsub (f a))
                                      (t : inftree A) (ht : acc dsub t) : acc dsub (node f t) :=
  acc.intro (node f t) (λ (y : inftree A) (hlt : dsub y (node f t)),
    have aux : ∀ z, dsub y z → node f t = z → acc dsub y, from
      λ z hlt, dsub.rec_on hlt
         (λ f₁ n t₁ (heq : (node f t = node f₁ t₁)),
           inftree.no_confusion heq (λ e₁ e₂, eq.rec_on e₁ (hf n)))
         (λ f₁ n t₁ (heq : (node f t = node f₁ t₁)),
           inftree.no_confusion heq (λ e₁ e₂, eq.rec_on e₂ ht)),
    aux (node f t) hlt rfl)

  definition dsub.leaf.acc {A : Type} (a : A) : acc dsub (leaf a) :=
  acc.intro (leaf a) (λ (y : inftree A) (hlt : dsub y (leaf a)),
    have aux : ∀ z, dsub y z → leaf a = z → acc dsub y, from
      λz hlt, dsub.rec_on hlt
        (λ f n t (heq : leaf a = node f t), inftree.no_confusion heq)
        (λ f n t (heq : leaf a = node f t), inftree.no_confusion heq),
    aux (leaf a) hlt rfl)

  definition dsub.wf (A : Type) : well_founded (@dsub A) :=
  well_founded.intro (λ (t : inftree A),
    rec_on t
      (λ a, dsub.leaf.acc a)
      (λ f t (ihf :∀a, acc dsub (f a)) (iht : acc dsub t), dsub.node.acc f ihf t iht))

end inftree
