/-!
`LE`, `LT` and the `Std.Is*Order` classes take a `Sort u` carrier, so propositions and
proof-indexed function types can carry order structure.
-/

instance (p : Prop) : LE p := ⟨fun _ _ => True⟩

example (p : Prop) (h₁ h₂ : p) : h₁ ≤ h₂ := trivial

instance : LE True := ⟨fun _ _ => True⟩

instance : Std.IsPreorder True where
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

example (a b c : True) : a ≤ b → b ≤ c → a ≤ c := by
  grind
