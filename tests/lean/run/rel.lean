import logic algebra.relation
open relation

namespace is_equivalence
  inductive cls {T : Type} (R : T → T → Prop) : Prop :=
  mk : is_reflexive R → is_symmetric R → is_transitive R → cls R

end is_equivalence

theorem and_inhabited_left {a : Prop} (b : Prop) (Ha : a) : a ∧ b ↔ b :=
iff.intro (take Hab, and.elim_right Hab) (take Hb, and.intro Ha Hb)

theorem test (a b c : Prop) (P : Prop → Prop) (H1 : a ↔ b) (H2 : c ∧ a) : c ∧ b :=
iff.subst H1 H2

theorem test2 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : Q ↔ (S ∧ Q) :=
iff.symm (and_inhabited_left Q H1)

theorem test3 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : R ↔ (S ∧ Q) :=
iff.subst (test2 Q R S H3 H1) H3

theorem test4 (Q R S : Prop) (H3 : R ↔ Q) (H1 : S) : R ↔ (S ∧ Q) :=
iff.subst (iff.symm (and_inhabited_left Q H1)) H3
