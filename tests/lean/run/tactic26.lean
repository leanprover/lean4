import standard
using tactic

inductive sum (A B : Type) : Type :=
| inl  : A → sum A B
| inr  : B → sum A B

theorem inl_inhabited {A : Type} (B : Type) (H : inhabited A) : inhabited (sum A B)
:= inhabited_elim H (λ a, inhabited_intro (inl B a))

theorem inr_inhabited (A : Type) {B : Type} (H : inhabited B) : inhabited (sum A B)
:= inhabited_elim H (λ b, inhabited_intro (inr A b))

definition my_tac := fixpoint (λ t, [ apply @inl_inhabited; t
                                    | apply @inr_inhabited; t
                                    | apply @num.inhabited_num
                                    ])

tactic_hint [inhabited] my_tac

theorem T : inhabited (sum false num.num)

