namespace test
universes u v w

structure lens (α : Type u) (β : Type v) :=
(get    : α → β)
(modify : α → (β → β) → α)
(set    : α → β → α := λ a b, modify a (λ _, b))

def lens.compose {α : Type u} {β : Type v} {σ : Type w} (t : lens β σ) (s : lens α β) : lens α σ :=
{ get    := t^.get ∘ s^.get,
  modify := λ a f, s^.modify a $ λ b, t^.modify b f,
  set    := λ a v, s^.modify a $ λ b, t^.set b v }

infix `∙`:1 := lens.compose

def fst {α β} : lens (α × β) α :=
{ get    := prod.fst,
  modify := λ ⟨a, b⟩ f, (f a, b) }

def snd {α β} : lens (α × β) β :=
{ get    := prod.snd,
  modify := λ ⟨a, b⟩ f, (a, f b) }

end test
