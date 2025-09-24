module
example : (if (!false) = true then id else id) false = false := by
  grind

opaque q (h : ¬ (!false) = true) : Bool → Bool

example : (if h : (!false) = true then id else q h) false = false := by
  grind

example [Decidable c] : (if c then id else id) false = false := by
  grind

opaque c : Prop
opaque r (h : ¬ c) : Bool → Bool
open Classical

@[grind =] theorem rax : r h x = x := sorry

example : (if h : c then id else r h) false = false := by
  grind
