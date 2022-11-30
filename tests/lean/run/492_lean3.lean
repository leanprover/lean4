class Foo (α : Type) : Type := (f : α)
def Foo.f' {α : Type} [c : Foo α] : α := Foo.f

#print Foo.f  -- def Foo.f : {α : Type} → [self : Foo α] → α
#print Foo.f' -- def Foo.f' : {α : Type} → [c : Foo α] → α

variable {α : Type} [c : Foo α]
#check c.f  -- ok
#check c.f' -- ok

structure Bar : Prop := (f : ∀ {m : Nat}, m = 0)
def Bar.f' : Bar → ∀ {m : Nat}, m = 0 := Bar.f

#print Bar.f  -- def Bar.f  : Bar → ∀ {m : ℕ}, m = 0
#print Bar.f' -- def Bar.f' : Bar → ∀ {m : ℕ}, m = 0

variable (h : Bar) (m : Nat)

#check (h.f : ∀ {m : Nat}, m = 0) -- ok
#check (h.f : m = 0)  -- ok
#check h.f (m := m)   -- ok
#check h.f (m := 0)   -- ok
#check (h.f' : m = 0) -- ok

theorem ex1 (n) : (h.f : n = 0) = h.f (m := n) :=
  rfl
