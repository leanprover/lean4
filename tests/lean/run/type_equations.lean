open nat

inductive Expr
| zero : Expr
| one  : Expr
| add  : Expr → Expr → Expr

namespace Expr

inductive direct_subterm : Expr → Expr → Prop
| add_1 : ∀ e₁ e₂ : Expr, direct_subterm e₁ (add e₁ e₂)
| add_2 : ∀ e₁ e₂ : Expr, direct_subterm e₂ (add e₁ e₂)

theorem direct_subterm_wf : well_founded direct_subterm :=
sorry
/-
begin
  constructor, intro e, induction e,
  repeat (constructor; intro y hlt; cases hlt; repeat assumption)
end
-/

definition subterm := tc direct_subterm

theorem subterm_wf : well_founded subterm :=
tc.wf direct_subterm_wf

local infix `+` := Expr.add

set_option pp.notation false

definition ev : Expr → nat
| zero             := 0
| one              := 1
| ((a : Expr) + b) := has_add.add (ev a) (ev b)

definition foo : Expr := add zero (add one one)

example : ev foo = 2 :=
rfl
end Expr
