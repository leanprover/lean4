import data.nat
open nat

inductive lift .{l} (A : Type.{l}) : Type.{l+1} :=
up : A → lift A

namespace lift
definition down {A : Type} (a : lift A) : A :=
rec (λ a, a) a

theorem down_up {A : Type} (a : A) : down (up a) = a :=
rfl

protected theorem induction_on {A : Type} {P : lift A → Prop} (a : lift A) (H : ∀ (a : A), P (up a)) : P a :=
rec H a

theorem up_down {A : Type} (a' : lift A) : up (down a') = a' :=
induction_on a' (λ a, rfl)

end lift

set_option pp.universes true
check nat
check lift nat
open lift
definition one1 : lift nat := up 1
