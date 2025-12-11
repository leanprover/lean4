module
example [BEq α] (xs ys : Vector α n) : (xs.toList == ys.toList) = (xs == ys) := by grind

example [LT α] {xs ys : Vector α n} : xs.toList < ys.toList ↔ xs < ys := by grind
