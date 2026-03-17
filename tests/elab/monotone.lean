class Preorder (α : Type u) extends LE α where
  le_refl  (a : α) : a ≤ a
  le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c

instance {α : Type u} {β : α → Type v} [(a : α) → Preorder (β a)] : Preorder ((a : α) → β a) where
  le f g := ∀ a, f a ≤ g a
  le_refl f  := fun a => Preorder.le_refl (f a)
  le_trans   := fun h₁ h₂ a => Preorder.le_trans (h₁ a) (h₂ a)

-- In Lean 3, we defined `monotone` using the strict implicit notation `{{ ... }}`.
-- Implicit lambdas in Lean 4 allow us to use the regular `{...}`
def Monotone [Preorder α] [Preorder β] (f : α → β) :=
  ∀ {a b}, a ≤ b → f a ≤ f b

theorem monotone_id [Preorder α] : Monotone (α := α) id :=
  fun h => h

theorem monotone_id' [Preorder α] : Monotone (α := α) id :=
  @fun a b h => h -- `@` disables implicit lambdas

theorem monotone_id'' [Preorder α] : Monotone (α := α) id :=
  fun {a b} (h : a ≤ b) => h -- `{a b}` disables implicit lambdas

theorem monotone_const [Preorder α] [Preorder β] (b : β) : Monotone (fun a : α => b) :=
  fun _ => Preorder.le_refl b

theorem monotone_comp [Preorder α] [Preorder β] [Preorder γ] {g : β → γ} {f : α → β} (m_g : Monotone g) (m_f : Monotone f) : Monotone (g ∘ f) :=
  fun h => m_g (m_f h)

theorem monotone_fun {α : Type u} {β : Type v} [Preorder α] [Preorder γ] {f : α → β → γ} (m : (b : β) → Monotone (fun a => f a b)) : Monotone f :=
  fun h b => m b h

theorem ex [Preorder α] {f g h : α → α} (m_h : Monotone h) (m_g : Monotone g) (m_f : Monotone f) : Monotone (h ∘ g ∘ f) :=
  monotone_comp m_h (monotone_comp m_g m_f) -- implicit lambdas in action here
