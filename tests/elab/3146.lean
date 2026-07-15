/-
  Verifies that `let`-bodies are reduced accordingly when trying to construct default fields.
  Fixes `#3146`
-/

def Product (m₁ : Type → Type) (m₂ : Type → Type) (α : Type) := m₁ α × m₂ α

instance [Monad m₁] [Monad m₂] : Monad (Product m₁ m₂) where
  pure x := (pure x, pure x)
  bind o f :=
    let y₁ := do f (← o.1) |>.1
    let y₂ := do f (← o.2) |>.2
    (y₁, y₂)
