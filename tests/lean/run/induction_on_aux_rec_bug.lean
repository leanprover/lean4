namespace test
universe variables u v
variables {α : Type u} {β : Type v}

inductive Perm : list α → list α → Prop
| nil   : Perm [] []
| skip  : Π (x : α) {l₁ l₂ : list α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
| swap  : Π (x y : α) (l : list α), Perm (y::x::l) (x::y::l)
| trans : Π {l₁ l₂ l₃ : list α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

namespace Perm
infix ~ := Perm

theorem eq_nil_of_Perm_nil {l₁ : list α} (p : [] ~ l₁) : l₁ = [] :=
have gen : ∀ (l₂ : list α) (p : l₂ ~ l₁), l₂ = [] → l₁ = [], from
  λ l₂ (p : l₂ ~ l₁), Perm.induction_on p
    (λ h,  h)
    (begin intros, contradiction end)
    (begin intros, contradiction end)
    (λ l₁ l₂ l₃ p₁ p₂ r₁ r₂ e, r₂ (r₁ e)),
gen [] p rfl

end Perm
end test
