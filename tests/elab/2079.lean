@[default_instance] instance : Pow Int Nat where
  pow m n := m ^ n

instance : @Trans Int Int Int (· < ·) (· < ·) (· < ·) where
  trans := sorry

example {n : Int} : n ^ 2 < 1 :=
  calc
    n ^ 2 < 1 ^ 2 := sorry
    _ < 1 := sorry
