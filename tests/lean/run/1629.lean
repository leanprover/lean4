/-!
# `dotParam` for controlling which parameter recieves the object of dot notation
https://github.com/leanprover/lean4/issues/1629
https://github.com/leanprover/lean4/issues/5482
-/

/-!
Example: normally `γ` would receive the object of dot notation, but we override it to the useful parameter.
-/

def Function.swap' {α β} {γ : α → β → Sort _} (f : dotParam <| (a : α) → (b : β) → γ a b)
  (b : β) (a : α) : γ a b := f a b

/-- info: 0 -/
#guard_msgs in #eval Nat.div.swap' 10 2
/-- info: 5 -/
#guard_msgs in #eval Nat.div.swap' 2 10

/-!
Example from https://github.com/leanprover/lean4/issues/5482
-/

class A (α : Type _) where
  a : α → Nat

def A.get {α : Type _} [A α] (self : dotParam α) : Nat := a self

structure B where
  b : Nat

instance : A B := ⟨B.b⟩

namespace B
export A (get)
end B

variable (b : B)

/-- info: b.get : Nat -/
#guard_msgs in #check b.get

/-!
Zulip example
https://leanprover.zulipchat.com/#narrow/channel/270676-lean4/topic/Function.20dot.20notation.20error/near/296865418
-/
class HasMem (α : outParam $ Type _) (β : Type _) where
  mem : α → β → Prop

infix:50 " ∈ " => HasMem.mem

def HasMem.Nonempty [HasMem α β] (self : dotParam β) : Prop :=
  ∃ x, x ∈ self

def Set (α : Type _) := α → Prop

instance : HasMem α (Set α) where
  mem x s := s x

namespace Set
export HasMem (Nonempty)
end Set

variable (s : Set α)
/-- info: s.Nonempty : Prop -/
#guard_msgs in #check s.Nonempty
