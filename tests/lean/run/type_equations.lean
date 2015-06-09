open nat

inductive expr :=
| zero : expr
| one  : expr
| add  : expr → expr → expr

namespace expr

inductive direct_subterm : expr → expr → Prop :=
| add_1 : ∀ e₁ e₂ : expr, direct_subterm e₁ (add e₁ e₂)
| add_2 : ∀ e₁ e₂ : expr, direct_subterm e₂ (add e₁ e₂)

theorem direct_subterm_wf : well_founded direct_subterm :=
begin
  constructor, intro e, induction e,
  repeat (constructor; intro y hlt; cases hlt; repeat assumption)
end

definition subterm := tc direct_subterm

theorem subterm_wf [instance] : well_founded subterm :=
tc.wf direct_subterm_wf

infix `+` := expr.add

set_option pp.notation false

definition ev : expr → nat
| zero             := 0
| one              := 1
| ((a : expr) + b) := ev a + ev b

definition foo : expr := add zero (add one one)

example : ev foo = 2 :=
rfl
end expr
