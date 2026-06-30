module
example {g : (Int → Bool) → Int → Bool} {f : Int → Bool} {a b : Int} (hab : a = b) :
    Nat.repeat g 1 f a = Nat.repeat g 1 f b := by
  grind
