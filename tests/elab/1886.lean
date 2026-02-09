structure U (α : Type) where
  a : α

theorem mk_inj (w : U.mk a = U.mk b) : a = b := by
  injection w
