def Int.leastOfBdd {P : Int → Prop} [DecidablePred P] (b : Int) (Hb : ∀ z : Int, P z → b ≤ z)
    (Hinh : ∃ z : Int, P z) : { lb : Int // P lb ∧ ∀ z : Int, P z → lb ≤ z } :=
  sorry

theorem Int.coe_leastOfBdd_eq {P : Int → Prop} [DecidablePred P] {b b' : Int} (Hb : ∀ z : Int, P z → b ≤ z)
    (Hb' : ∀ z : Int, P z → b' ≤ z) (Hinh : ∃ z : Int, P z) :
    (leastOfBdd b Hb Hinh : Int) = leastOfBdd b' Hb' Hinh := by
  grind

example (f : Int → Int) (x y : Int) : x ≤ y → y ≤ x → f x = f y := by
  grind -lia -linarith
