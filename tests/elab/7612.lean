
theorem extracted_1 (x y : BitVec 9) :
    (y - y.srem x).sdiv x = y.sdiv x := by
  ac_nf
  sorry
