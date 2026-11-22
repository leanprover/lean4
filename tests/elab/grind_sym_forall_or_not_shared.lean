/-!
The `Sym.simp`-based `grind` normalizer rewrites `∀ x, p x ∨ ¬ q x` using `¬ q x = (q x → False)`.
The `False` it introduces must be the maximally shared one: `sym.debug` used to report an
`assertShared` violation here, and `grind` failed.
-/
set_option backward.grind.normalizer false
set_option sym.debug true

example (p q : Nat → Prop) (h : ∀ x, p x ∨ ¬ q x) (h₂ : q 0) : p 0 := by
  grind

example (p q : Nat → Prop) (h : ∀ x, ¬ q x ∨ p x) (h₂ : q 0) : p 0 := by
  grind
