def is_smooth {α β} (f : α → β) : Prop := sorry

class IsSmooth {α β} (f : α → β) : Prop where
  (proof : is_smooth f)

instance identity : IsSmooth fun a : α => a := sorry
instance const (b : β) : IsSmooth fun a : α => b := sorry
instance swap (f : α → β → γ) [∀ a, IsSmooth (f a)] : IsSmooth (λ b a => f a b) := sorry
instance parm (f : α → β → γ) [IsSmooth f] (b : β) : IsSmooth (λ a => f a b) := sorry
instance comp (f : β → γ) (g : α → β) [IsSmooth f] [IsSmooth g] : IsSmooth (fun a => f (g a)) := sorry
instance diag (f : β → δ → γ) (g : α → β) (h : α → δ) [IsSmooth f] [∀ b, IsSmooth (f b)] [IsSmooth g] [IsSmooth h] : IsSmooth (λ a => f (g a) (h a)) := sorry

set_option trace.Meta.synthInstance true
set_option trace.Meta.synthInstance.unusedArgs true
example (f : β → δ → γ) [IsSmooth f] (d : δ) : IsSmooth (λ (g : α → β) a => f (g a) d) := by infer_instance
