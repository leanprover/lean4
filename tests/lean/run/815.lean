def is_smooth {α β} (f : α → β) : Prop := sorry

class IsSmooth {α β} (f : α → β) : Prop where
  (proof : is_smooth f)

instance identity : IsSmooth fun a : α => a := sorry
instance const (b : β) : IsSmooth fun a : α => b := sorry
instance swap (f : α → β → γ) [∀ a, IsSmooth (f a)] : IsSmooth (λ b a => f a b) := sorry
instance parm (f : α → β → γ) [IsSmooth f] (b : β) : IsSmooth (λ a => f a b) := sorry
instance comp (f : β → γ) (g : α → β) [IsSmooth f] [IsSmooth g] : IsSmooth (fun a => f (g a)) := sorry
instance diag (f : β → δ → γ) (g : α → β) (h : α → δ) [IsSmooth f] [∀ b, IsSmooth (f b)] [IsSmooth g] [IsSmooth h] : IsSmooth (λ a => f (g a) (h a)) := sorry

example (f : β → δ → γ) [IsSmooth f] (g : α → β) [IsSmooth g] (d : δ) : IsSmooth (λ a => f (g a) d) := by infer_instance
example (f : β → δ → γ) [IsSmooth f] (g : α → β) [IsSmooth g] : IsSmooth (λ a d => f (g a) d) := by infer_instance
example (f : β → δ → γ) [IsSmooth f] (g : α → β) [IsSmooth g] (h : α → α) [IsSmooth h] (d : δ) : IsSmooth (λ a => f (g (h a)) d) := by infer_instance
example (f : α → β → γ) [∀ a, IsSmooth (f a)] : IsSmooth (λ b a => f a b) := by infer_instance
example (f : α → β → γ → δ) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ c b a => f a b c) := by infer_instance
example (f : α → β → γ → δ) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ c a b => f a b c) := by infer_instance
example (f : α → β → γ → δ → ε) [∀ a b c, IsSmooth (f a b c)] : IsSmooth (λ d a b c => f a b c d) := by infer_instance
example (f : α → β → γ) [IsSmooth f] (b : β) : IsSmooth (λ a => f a b) := by infer_instance
example (f : α → β → γ → δ) [IsSmooth f] (b : β) (c : γ) : IsSmooth (λ a => f a b c) := by infer_instance
example (f : α → β → γ → δ) [IsSmooth f] (b : β) : IsSmooth (λ a c => f a b c) := by infer_instance
example (f : α → β → γ → δ) [IsSmooth f] (c : γ) : IsSmooth (λ a b => f a b c) := by infer_instance
example (f : α → β → γ → δ) (b : β) [IsSmooth (λ a => f a b)] : IsSmooth (λ a c => f a b c) := by infer_instance
example (f : α → β → γ) (g : δ → ε → α) (h : δ → ε → β) [IsSmooth f] [∀ a, IsSmooth (f a)] [IsSmooth g] [IsSmooth h] : IsSmooth (λ x y => f (g x y) (h x y)) := by infer_instance
example (f : β → δ → γ) (g : α → β) [IsSmooth f] [∀ b, IsSmooth (f b)] [IsSmooth g] (a : α): IsSmooth (λ (h : α → δ) => f (g a) (h a)) := by infer_instance
example (f : β → δ → γ) (h : α → δ) [IsSmooth f] : IsSmooth (λ (g : α → β) a => f (g a) (h a)) := by infer_instance
example (f : β → δ → γ) [IsSmooth f] (d : δ) : IsSmooth (λ (g : α → β) a => f (g a) d) := by infer_instance
example (f : β → γ) (g : β → β) [IsSmooth f] [IsSmooth g] : IsSmooth (fun x => f (g (g x))) := by infer_instance
example (f : α → β → γ) [∀ a, IsSmooth (f a)] : IsSmooth (λ b a => f a b) := by infer_instance
example (f : α → β → γ → δ) [∀ a b, IsSmooth (f a b)] : IsSmooth (λ c a b => f a b c) := by infer_instance
example (f : α → β → γ → δ → ε) [∀ a b c, IsSmooth (f a b c)] : IsSmooth (λ d a b c => f a b c d) := by infer_instance
example (f : β → δ → γ) [IsSmooth f] (g : α → β) [IsSmooth g] (d : δ) : IsSmooth (λ a => f (g a) d) := by infer_instance
example (f : β → δ → γ) [IsSmooth f] (g : α → β) [IsSmooth g] : IsSmooth (λ a d => f (g a) d) := by infer_instance
example (f : δ → β → γ) [∀ d, IsSmooth (f d)] (g : α → β) [IsSmooth g] : IsSmooth (λ a d => (f d (g a))) := by infer_instance


-- Recall Function.comp is not reducible anymore
instance (f : β → γ) (g : α → β) [IsSmooth f] [IsSmooth g] : IsSmooth (f ∘ g) := by
  delta Function.comp
  infer_instance

example (f : β → γ) (g : α → β) [IsSmooth f] [IsSmooth g] : IsSmooth (f ∘ g) := by infer_instance

example (f : β → γ) [IsSmooth f] : IsSmooth λ (g : α → β) => (f ∘ g) := by
  delta Function.comp
  infer_instance
