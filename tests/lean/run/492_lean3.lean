class foo (α : Type) : Type := (f : α)
def foo.f' {α : Type} [c : foo α] : α := foo.f

#print foo.f  -- def foo.f : {α : Type} → [self : foo α] → α
#print foo.f' -- def foo.f' : {α : Type} → [c : foo α] → α

variable {α : Type} [c : foo α]
#check c.f  -- ok
#check c.f' -- ok

structure bar : Prop := (f : ∀ {m : Nat}, m = 0)
def bar.f' : bar → ∀ {m : Nat}, m = 0 := bar.f

#print bar.f  -- def bar.f  : bar → ∀ {m : ℕ}, m = 0
#print bar.f' -- def bar.f' : bar → ∀ {m : ℕ}, m = 0

variable (h : bar) (m : Nat)

#check (h.f : ∀ {m : Nat}, m = 0) -- ok
#check (h.f : m = 0)  -- ok
#check h.f (m := m)   -- ok
#check h.f (m := 0)   -- ok
#check (h.f' : m = 0) -- ok

theorem ex1 (n) : (h.f : n = 0) = h.f (m := n) :=
  rfl
