/-!
Test that `Iff.rfl` is tried by the `rfl` tactic.
-/
universe u v w

class L (F : Sort u) (α : outParam (Sort v)) (β : outParam (α → Sort w)) where
  coe : F → ∀ a : α, β a

instance {F : Sort u} {α : Sort v} {β : α → Sort w} [L F α β] :
    CoeFun F (fun _ ↦ ∀ a : α, β a) where coe := @L.coe _ _ β _

instance {π : Nat → Type u} [∀ i, LE (π i)] : LE (∀ i, π i) where le x y := ∀ i, x i ≤ y i

structure S (α : Nat → Type u) where
variable {α : Nat → Type u} [∀ i, LE (α i)]
instance : L (S α) Nat α := sorry
instance : LE (S α) := ⟨fun f g ↦ ∀ i, f i ≤ g i⟩

example : ∀ {a b : S α}, L.coe a ≤ L.coe b ↔ a ≤ b := by rfl
