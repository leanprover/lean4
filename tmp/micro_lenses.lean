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
  modify := λ ⟨a, b⟩ f, (f a, b),
  set    := λ ⟨a, b⟩ a', (a', b)}

def snd {α β} : lens (α × β) β :=
{ get    := prod.snd,
  modify := λ ⟨a, b⟩ f, (a, f b),
  set    := λ ⟨a, b⟩ b', (a, b') }

def idx {α} {n} (i : fin n) : lens (array α n) α :=
{ get    := λ a,   a^.read i,
  modify := λ a f, a^.write i $ f $ a^.read i,
  set    := λ a b, a^.write i b }

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
  modify := modify_ith i }

set_option trace.array.update true

def f (a : array nat 10 × array bool 5) : array nat 10 × array bool 5 :=
(idx 2 ∙ snd)^.set ((idx 1 ∙ fst)^.set a 1) ff

#eval f (mk_array 10 0, mk_array 5 tt)

#eval (idx 2 ∙ snd)^.set ((idx 1 ∙ fst)^.set (mk_array 10 0, mk_array 5 tt) 1) ff

#eval let p₀ := (mk_array 10 0, mk_array 5 tt),
          p₁ := (idx 1 ∙ fst)^.set p₀ 1,
          p₂ := (idx 2 ∙ snd)^.set p₁ ff in
        p₂

example : (fst ∙ nth 1)^.set [(1, 2), (3, 4), (0, 3)] 30 = [(1, 2), (30, 4), (0, 3)] :=
rfl

example : (snd ∙ nth 1)^.get [(1, 2), (3, 4), (0, 3)] = 4 :=
rfl

def micro_lens (f : Type u → Type w) [functor f] (α β : Type u) :=
(β → f β) → α → f α

def micro_lens.compose {f : Type u → Type w} [functor f] {α β δ: Type u} (l₁ : micro_lens f β δ) (l₂ : micro_lens f α β) : micro_lens f α δ :=
λ g a, l₂ (l₁ g) a

instance : applicative id :=
{pure := λ _ a, a,
 seq  := λ _ _ f a, f a}

def micro_lens.modify {α β : Type u} (l : micro_lens id α β) (a : α) (b : β → β) : α :=
l b a

def micro_lens.set {α β : Type u} (l : micro_lens id α β) (a : α) (b : β) : α :=
l (λ _, b) a

def fconst (α : Type v) (β : Type u) : Type v :=
α

instance (α : Type v) : functor (fconst α) :=
{map := λ (β δ : Type u) f a, a}

def micro_lens.get {α β : Type u} (l : micro_lens (fconst β) α β) (a : α) : β :=
l (λ b, b) a

def pi₁ {f : Type u → Type w} [functor f] {α β : Type u} : micro_lens f (α × β) α :=
λ g ⟨a, b⟩, (λ x, (x, b)) <$> g a

def pi₂ {f : Type u → Type w} [functor f] {α β : Type u} : micro_lens f (α × β) β :=
λ g ⟨a, b⟩, (λ x, (a, x)) <$> g b

#eval micro_lens.get pi₁ (10, 20)
#eval micro_lens.get pi₂ (10, 20)
#eval micro_lens.set pi₂ (10, 20) 100
#eval micro_lens.set (pi₁ ∘ pi₁) ((10, 20), 30) 1
#eval micro_lens.set (pi₁ ∘ pi₂) ((10, 20), 30) 1
#eval micro_lens.set pi₂ (((10, 20), 30) : (nat × nat) × nat) 1
#eval micro_lens.get (pi₁ ∘ pi₂) ((10, 20), 30)
#eval micro_lens.modify (pi₁ ∘ pi₂) ((10, 20), 30) (+1)
