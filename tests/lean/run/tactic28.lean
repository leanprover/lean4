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

infixl `..`:10 := append

notation `(` h `|` r:(foldl `|` (e r, tactic.or_else r e) h) `)` := r
infixl `;`:15 := tactic.and_then
reveal inl_inhabited inr_inhabited
definition my_tac := repeat (trace "iteration"; state;
                              (  apply @inl_inhabited; trace "used inl"
                              .. apply @inr_inhabited; trace "used inr"
                              .. apply @num.is_inhabited; trace "used num")) ; now


tactic_hint my_tac

theorem T : inhabited (sum false num)

end foo
