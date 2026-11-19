module

set_option grind.debug true in
theorem test {β α} {γ : β → Sort v} {f : α → β} {g : β → α}
    (h : Function.LeftInverse g f) (C : ∀ a : α, γ (f a)) (a : α) :
    cast (congrArg (fun a ↦ γ (f a)) (h a)) (C (g (f a))) = C a := by
  grind
