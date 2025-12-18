/- Implicit arguments and universe polymorphism -/

def f (α β : Sort u) (a : α) (b : β) : α := a

#eval f Nat String 1 "hello"
-- 1

def g {α β : Sort u} (a : α) (b : β) : α := a

#eval g 1 "hello"

def h (a : α) (b : β) : α := a

#check g
-- ?m.1 → ?m.2 → ?m.1
#check @g
-- {α β : Sort u} → α → β → α
#check @h
-- {α : Sort u_1} → {β : Sort u_2} → α → β → α
#check g (α := Nat) (β := String)
-- Nat → String → Nat
