import logic struc.relation
using relation

namespace is_equivalence

  inductive class {T : Type} (R : T → T → Type) : Prop :=
  | mk : is_reflexive.class R → is_symmetric.class R → is_transitive.class R → class R

  theorem is_reflexive {T : Type} {R : T → T → Type} {C : class R} : is_reflexive.class R :=
  class_rec (λx y z, x) C

  theorem is_symmetric {T : Type} {R : T → T → Type} {C : class R} : is_symmetric.class R :=
  class_rec (λx y z, y) C

  theorem is_transitive {T : Type} {R : T → T → Type} {C : class R} : is_transitive.class R :=
  class_rec (λx y z, z) C

end is_equivalence

instance is_equivalence.is_reflexive
instance is_equivalence.is_symmetric
instance is_equivalence.is_transitive

theorem and_inhabited_left {a : Prop} (b : Prop) (Ha : a) : a ∧ b ↔ b :=
iff_intro (take Hab, and_elim_right Hab) (take Hb, and_intro Ha Hb)

theorem test (a b c : Prop) (P : Prop → Prop) (H1 : a ↔ b) (H2 : c ∧ a) : c ∧ b :=
gensubst.subst H1 H2

theorem test2 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : Q ↔ (S ∧ Q) :=
relation.operations.symm (and_inhabited_left Q H1)

theorem test3 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : R ↔ (S ∧ Q) :=
gensubst.subst (test2 Q R S H3 H1) H3

-- the composition of test2' and test3' fails
theorem test4 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : R ↔ (S ∧ Q) :=
gensubst.subst (relation.operations.symm (and_inhabited_left Q H1)) H3
