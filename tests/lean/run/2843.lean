axiom abs : Int → Int

axiom abs_eq_self {a : Int }: abs a = a ↔ 0 ≤ a

example (x : Int) : False := by
  let y := x/2
  have h : 0 ≤ y := sorry
  have : abs y = y := by
    -- generalize y = z at *
    simp (config := {zeta := false}) only [abs_eq_self.mpr h]
  sorry

example (x : Int) : False := by
  let y := x/2
  have h : 0 ≤ y := sorry
  have : abs y = y := by
    simp only [abs_eq_self.mpr h]
  sorry
