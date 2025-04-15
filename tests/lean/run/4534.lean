universe u

class MyClass (α : Type u) extends LE α where
  sup : α → α → α
  le_refl : ∀ a : α, a ≤ a
  sup_of_le_left : ∀ a b : α, b ≤ a → sup a b = a

instance : MyClass Prop where
  le p q := p → q
  sup p q := p ∨ q
  le_refl _ := id
  sup_of_le_left _ _ h := propext ⟨Or.rec id h, Or.inl⟩

/--
info: Try this: simp only [MyClass.le_refl, MyClass.sup_of_le_left]
-/
#guard_msgs in
example : MyClass.sup False False = False := by
  simp? [MyClass.sup_of_le_left, MyClass.le_refl]
