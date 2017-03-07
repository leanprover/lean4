universes u v w

structure lens (α : Type u) (β : Type v) :=
(get    : α → β)
(modify : α → (β → β) → α)
(set    : α → β → α := λ a b, modify a (λ _, b))

def lens.compose {α : Type u} {β : Type v} {σ : Type w} (t : lens β σ) (s : lens α β) : lens α σ :=
{ get    := t^.get ∘ s^.get,
  set    := λ a d, s^.set a (t^.set (s^.get a) d),
  modify := λ a f, s^.set a (t^.modify (s^.get a) f) }

infix `∙`:1 := lens.compose

def fst {α β} : lens (α × β) α :=
{ get    := prod.fst,
  modify := λ p f, (f p.1, p.2) }

def snd {α β} : lens (α × β) β :=
{ get    := prod.snd,
  modify := λ p f, (p.1, f p.2) }

def modify_ith {α} : nat → list α → (α → α) → list α
| _     []     f := []
| 0     (b::l) f := f b :: l
| (n+1) (b::l) f := b :: modify_ith n l f

def ith {α} [inhabited α] : nat → list α → α
| 0     (a::l) := a
| (n+1) (a::l) := ith n l
| _     _      := default α

def nth {α} [inhabited α] (i : nat) : lens (list α) α :=
{ get    := ith i,
  modify := modify_ith i}

example : (fst ∙ nth 1)^.set [(1, 2), (3, 4), (0, 3)] 30 = [(1, 2), (30, 4), (0, 3)] :=
rfl

example : (snd ∙ nth 1)^.get [(1, 2), (3, 4), (0, 3)] = 4 :=
rfl
