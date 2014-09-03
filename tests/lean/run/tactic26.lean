import logic
open tactic inhabited

inductive sum (A : Type) (B : Type) : Type :=
inl  : A → sum A B,
inr  : B → sum A B

theorem inl_inhabited {A : Type} (B : Type) (H : inhabited A) : inhabited (sum A B)
:= inhabited_destruct H (λ a, inhabited_mk (inl B a))

theorem inr_inhabited (A : Type) {B : Type} (H : inhabited B) : inhabited (sum A B)
:= inhabited_destruct H (λ b, inhabited_mk (inr A b))

definition my_tac := fixpoint (λ t, [ apply @inl_inhabited; t
                                    | apply @inr_inhabited; t
                                    | apply @num.num_inhabited
                                    ])

tactic_hint [inhabited] my_tac

theorem T : inhabited (sum false num.num)
