opaque f (a : Array Bool) (i : Nat) (h : i < a.size) : Bool

set_option trace.grind.eqc true

example : (p ∨ ∀ h : i < a.size, f a i h) → (hb : i < b.size) → a = b → ¬p → f b i hb := by
  grind
