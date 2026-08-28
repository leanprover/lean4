example: ¬ n + 1 = n := λ h => nomatch h


inductive Term (L: Nat → Type) (n : Nat) : Nat → Type _
| var  (k: Fin n)                           : Term L n 0
| func (f: L l)                             : Term L n l
| app  (t: Term L n (l + 1)) (s: Term L n 0): Term L n l

namespace Term

inductive SubTermOf: Term L n l₁ → Term L n l₂ → Prop
| refl: SubTermOf t t
| appL: SubTermOf t s₁ → SubTermOf t (app s₁ s₂)
| appR: SubTermOf t s₂ → SubTermOf t (app s₁ s₂)

theorem app_SubTermOf {t₁: Term L n (l+1)}
  (h: (app t₁ t₂).SubTermOf t₃):
  t₁.SubTermOf t₃ ∧ t₂.SubTermOf t₃ := by
  match h with
  | .appR h => have := app_SubTermOf h; exact ⟨.appR this.1, .appR this.2⟩
  | .appL h => have := app_SubTermOf h; exact ⟨.appL this.1, .appL this.2⟩
  | .refl => exact ⟨.appL .refl, .appR .refl⟩

mutual
  theorem not_app_SubTermOf_left (t: Term L n (l+1)) : ¬ (app t s).SubTermOf t :=
    fun
    | .appR h => have := app_SubTermOf h; not_app_SubTermOf_right _ this.1
    | .appL h => have := app_SubTermOf h; not_app_SubTermOf_left  _ this.1

  theorem not_app_SubTermOf_right (s: Term L n 0) : ¬ (app t s).SubTermOf s :=
    fun
    | .appR h => have := app_SubTermOf h; not_app_SubTermOf_right _ this.2
    | .appL h => have := app_SubTermOf h; not_app_SubTermOf_left  _ this.2
end
