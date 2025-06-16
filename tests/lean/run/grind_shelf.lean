class Shelf (α : Type u) where
  act : α → α → α
  self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z)

class UnitalShelf (α : Type u) extends Shelf α, One α where
  one_act : ∀ a : α, act 1 a = a
  act_one : ∀ a : α, act a 1 = a

infixr:65 " ◃ " => Shelf.act

-- Mathlib proof from UnitalShelf.act_act_self_eq
example {S} [UnitalShelf S] (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by rw [UnitalShelf.act_one]
  rw [h, ← Shelf.self_distrib, UnitalShelf.act_one]

attribute [grind =] UnitalShelf.one_act UnitalShelf.act_one

-- We actually want the reverse direction of `Shelf.self_distrib`, so don't use the `grind_eq` attribute.
grind_pattern Shelf.self_distrib => self.act (self.act x y) (self.act x z)

-- Proof using `grind`:
example {S} [UnitalShelf S] (x y : S) : (x ◃ y) ◃ x = x ◃ y := by
  have h : (x ◃ y) ◃ x = (x ◃ y) ◃ (x ◃ 1) := by grind
  grind
