structure Trans₁ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) where
  trans : r a b → s b c → t a c

structure Trans₂ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) :
    Sort (max 1 a b c u v w) where
  trans : r a b → s b c → t a c

inductive Trans₃ {α : Sort a} {β : Sort b} {γ : Sort c}
    (r : α → β → Sort u) (s : β → γ → Sort v) (t : outParam (α → γ → Sort w)) :
    Sort (max 1 a b c u v w) where
  | mk : (∀ a b c, r a b → s b c → t a c) → Trans₃ r s t
