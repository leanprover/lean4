def f : List Nat → List Nat → Nat
  | _, 1 :: _ :: _ => 1
  | _, _ :: _ => 2
  | _, _  => 0

example : z = a :: as → y = z → f x y > 0 := by
  grind [f.eq_def]
