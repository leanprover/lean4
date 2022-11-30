/- Simplifier -/

def mkSymm (xs : List α) :=
  xs ++ xs.reverse

@[simp] theorem reverse_mkSymm : (mkSymm xs).reverse = mkSymm xs := by
  simp [mkSymm]

theorem tst : (xs ++ mkSymm ys).reverse = mkSymm ys ++ xs.reverse := by
  simp

#print tst
-- Lean reverse_mkSymm, and List.reverse_append
