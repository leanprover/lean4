#lang lean4

universes u

def f {α : Type u} [HasBeq α] (xs : List α) (y : α) : α := do
for x in xs do
  if x == y then
    return x
return y

structure S :=
(key val : Nat)

instance : HasBeq S :=
⟨fun a b => a.key == b.key⟩

theorem ex1 : f (α := S) [⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩] ⟨3, 0⟩ = ⟨3, 4⟩ :=
rfl

theorem ex2 : f (α := S) [⟨1, 2⟩, ⟨3, 4⟩, ⟨5, 6⟩] ⟨4, 10⟩ = ⟨4, 10⟩ :=
rfl
