axiom foo {p : Prop} {x : BitVec 32} (h : (!x == x + 0#32) = true) : p

theorem add_eq_sub_not_sub_one (x : BitVec 32) (h : (!x == x + (1#32 + 4294967295#32)) = true) : False := by
  simp only [BitVec.reduceAdd] at h
  exact foo h -- this works

theorem add_eq_sub_not_sub_one' (x : BitVec 32) (h : (!x == x + 1#32 + 4294967295#32) = true) : False := by
  ac_nf0 at h
  simp only [BitVec.reduceAdd] at h
  exact foo h -- this used to hang
