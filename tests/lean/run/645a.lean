open bool

definition to_pred {A : Type} (p : A → bool) : A → Prop :=
λ a, p a = tt

definition to_pred_dec₁ [instance] {A : Type} (p : A → bool)
                : decidable_pred (to_pred p) :=
begin
  intro a, unfold to_pred,
  induction p a,
    right, contradiction,
    left, reflexivity
end

definition to_pred_dec₂ [instance] {A : Type} (p : A → bool)
                : decidable_pred (to_pred p) :=
begin
  intro a, unfold to_pred,
  cases p a,
    right, contradiction,
    left, reflexivity
end
