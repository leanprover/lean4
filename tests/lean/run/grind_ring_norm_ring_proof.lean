example [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α] (a b c : α) :
  (if a - b ≤ -(a - b) then -(a - b) else a - b) ≤
  ((if a - c ≤ -(a - c) then -(a - c) else a - c) + if c - d ≤ -(c - d) then -(c - d) else c - d) +
    if b - d ≤ -(b - d) then -(b - d) else b - d := by
  split <;> split <;> split <;> split <;> grind
