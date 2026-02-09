example {x y : Int} : y = 0 → (x.fdiv y) = 0 := by grind
example {x y : Int} : y = 0 → (x.tdiv y) = 0 := by grind
example {x y : Int} : y = 0 → (x.fmod y) = x := by grind
example {x y : Int} : y = 1 → (x.fdiv (2 - y)) = x := by grind
example {x : Int} : x > 0 → x.sign = 1 := by grind
example {x : Int} : x < 0 → x.sign = -1 := by grind
example {x y : Int} : x.sign = 0 → x*y = 0 := by grind
