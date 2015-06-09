import logic data.nat.basic
open nat

inductive inftree (A : Type) :=
| leaf : A → inftree A
| node : (nat → inftree A) → inftree A

namespace inftree
  inductive dsub {A : Type} : inftree A → inftree A → Prop :=
  intro : Π (f : nat → inftree A) (a : nat), dsub (f a) (node f)

  definition dsub.node.acc {A : Type} (f : nat → inftree A) (H : ∀a, acc dsub (f a)) : acc dsub (node f) :=
  acc.intro (node f) (λ (y : inftree A) (hlt : dsub y (node f)),
    have aux : ∀ z, dsub y z → node f = z → acc dsub y, from
      λ z hlt, dsub.rec_on hlt (λ (f₁ : nat → inftree A) (a : nat) (eq₁ : node f = node f₁),
        inftree.no_confusion eq₁ (λe, eq.rec_on e (H a))),
    aux (node f) hlt rfl)

  definition dsub.leaf.acc {A : Type} (a : A) : acc dsub (leaf a) :=
  acc.intro (leaf a) (λ (y : inftree A) (hlt : dsub y (leaf a)),
    have aux : ∀ z, dsub y z → leaf a = z → acc dsub y, from
      λz hlt, dsub.rec_on hlt (λ f n (heq : leaf a = node f), inftree.no_confusion heq),
    aux (leaf a) hlt rfl)

  definition dsub.wf (A : Type) : well_founded (@dsub A) :=
  well_founded.intro (λ (t : inftree A),
    inftree.rec_on t
      (λ a, dsub.leaf.acc a)
      (λ f (ih :∀a, acc dsub (f a)), dsub.node.acc f ih))

  theorem dsub.wf₂ (A : Type) : well_founded (@dsub A) :=
  begin
    constructor, intro t, induction t with a f ih ,
     {constructor, intro y hlt, cases hlt},
     {constructor, intro y hlt, cases hlt, exact ih a}
  end

end inftree
