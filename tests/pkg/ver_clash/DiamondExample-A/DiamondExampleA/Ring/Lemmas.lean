module

public import DiamondExampleA.Ring.Defs

namespace Ring

public theorem poorly_named_lemma [Ring α] : ∀ a b c : α, a + (b + c) = b + (a + c) := by
  intros a b c
  rw [← add_assoc a b c]
  rw [add_comm a b]
  rw [add_assoc b a c]

end Ring
