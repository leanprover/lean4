structure FoldImpl (α β : Type u) where
  γ   : Type u
  x₀  : γ
  f   : γ → α → γ
  out : γ → β

inductive R : FoldImpl α β → FoldImpl α β → Prop where
  | intro {γ γ' x₀ y₀ f g out out'} : R ⟨γ, x₀, f, out⟩ ⟨γ', y₀, g, out'⟩

#print R

#check @R.intro
-- @R.intro : ∀ {α β γ γ' : Type u_1} {x₀ : γ} {y₀ : γ'} {f : γ → α → γ} {g : γ' → α → γ'} {out : γ → β} {out' : γ' → β},
--   R { γ := γ, x₀ := x₀, f := f, out := out } { γ := γ', x₀ := y₀, f := g, out := out' }

namespace Ex2

inductive R : FoldImpl α β → FoldImpl α β → Prop where
  | intro : R ⟨γ, x₀, f, out⟩ ⟨γ', y₀, g, out'⟩

#print R

end Ex2
