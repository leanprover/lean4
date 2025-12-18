/- Simplifier -/

def mk_symm (xs : List α) :=
  xs ++ xs.reverse

@[simp] theorem reverse_mk_symm : (mk_symm xs).reverse = mk_symm xs := by
  simp [mk_symm]

theorem tst : (xs ++ mk_symm ys).reverse = mk_symm ys ++ xs.reverse := by
  simp

#print tst
-- Lean reverse_mk_symm, and List.reverse_append
