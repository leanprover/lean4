import logic data.num
open tactic inhabited

namespace foo
inductive sum (A : Type) (B : Type) : Type :=
| inl  : A → sum A B
| inr  : B → sum A B

theorem inl_inhabited {A : Type} (B : Type) (H : inhabited A) : inhabited (sum A B)
:= inhabited.destruct H (λ a, inhabited.mk (sum.inl B a))

theorem inr_inhabited (A : Type) {B : Type} (H : inhabited B) : inhabited (sum A B)
:= inhabited.destruct H (λ b, inhabited.mk (sum.inr A b))

definition my_tac := fixpoint (λ t, ( apply @inl_inhabited; t
                                    | apply @inr_inhabited; t
                                    | apply @num.is_inhabited
                                    ))

tactic_hint my_tac

theorem T : inhabited (sum false num)

end foo
