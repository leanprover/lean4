import Simplc

-- This seems like a weird corner case. The discharger doesn't simplify `h` because it is used.
example (n m : Nat) (i : Fin n) (h : 0 + n = m + n) : Fin.natAdd m i = Fin.cast (by omega) i := by
  simp at h
  ext
  simpa
simp_lc whitelist Fin.cast_natAdd_left Fin.cast_natAdd_zero
simp_lc whitelist Fin.cast_addNat_right Fin.cast_addNat_zero

#guard_msgs (drop info) in
simp_lc check in Fin
