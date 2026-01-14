module
structure DepThing {α : Type u} (l : List α) : Type u where
  suffix : List α
  property : suffix = l

example (n : Nat) (c : DepThing (List.range' 1 (n/1))) (h : 0 < c.suffix.length) : True :=  by
  grind

opaque p (n : Int) : Type
opaque q (n : Int) (h : p n) : Prop
example (h : p (a / 0)) : q (a / 0) h → q (a / 0) h := by grind
example (h : p (a / -1)) : q (a / -1) h → q (a / -1) h := by grind
example (h : p (a / 1)) : q (a / 1) h → q (a / 1) h := by grind
example (h₁ : p (a / 0)) (h₂ : p 0) : h₁ ≍ h₂ → q (a / 0) h₁ → q 0 h₂ := by grind
example (h₁ : p (a / 1)) (h₂ : p a) : h₁ ≍ h₂ → q (a / 1) h₁ → q (a) h₂ := by grind
example (h₁ : p (a / -1)) (h₂ : p (-a)) : h₁ ≍ h₂ → q (a / -1) h₁ → q (-a) h₂ := by grind
