import data.list

constant A : Type₁
constant B : Type₁
constant coe : A → B
attribute coe [coercion]
variable f : B → B
variable a : A
set_option pp.coercions true
check f a

constant C : Type₁
variable g : (C → B) → B
variable h : C → A
check g h

definition tst (g : C → B) : Prop := g = h

open bool list

definition bool_to_Prop [coercion] [reducible] (b : bool) : Prop := b = tt

definition bpred_dec [instance] {A : Type} (p : A → bool) : ∀ a, decidable (p a = tt) :=
begin
  intro a,
  eapply (bool.rec_on (p a)),
    right, contradiction,
    left, reflexivity
end

definition negb : bool → bool := bool.rec tt ff

check filter negb [tt, ff, tt, ff]

eval filter negb [tt, ff, tt, ff]

example : filter negb [tt, ff, tt, ff] = [ff, ff] :=
rfl
