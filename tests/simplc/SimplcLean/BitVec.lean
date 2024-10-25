import Simplc

simp_lc ignore BitVec.getLsbD_ge
simp_lc ignore BitVec.getMsbD_ge

-- TODO: this one indicates some work required around `Fin.ofNat'`
simp_lc whitelist BitVec.ofFin_sub BitVec.sub_zero

-- TODO: move to library
@[simp] theorem Fin.ofNat'_zero (n : Nat) [NeZero n] : Fin.ofNat' n 0 = 0 := rfl

namespace BitVec

-- @[simp] theorem setWidth_setWidth (x : BitVec u) (w : Nat) (h : u ≤ v ∨ w ≤ v) : setWidth w (setWidth v x) = setWidth w x := by
--   ext
--   simp only [getLsbD_setWidth, Fin.is_lt, decide_True, Bool.true_and, Bool.and_iff_right_iff_imp,
--     decide_eq_true_eq]
--   intro h
--   replace h := lt_of_getLsbD h
--   omega

-- TODO: re-evaluate these (appeared while moving `Simplc` into Lean.)
-- simp_lc whitelist BitVec.umod_eq_and BitVec.umod_self
-- simp_lc whitelist BitVec.udiv_one BitVec.udiv_self
-- simp_lc whitelist BitVec.udiv_eq_and BitVec.udiv_self

-- This would be resolved by simply using `setWidth` instead of `cast`!
-- TODO: discuss with Tobias et al.
example (h : v = w) (x : BitVec v) : cast h x = setWidth w x := by
  ext
  simp
simp_lc whitelist BitVec.setWidth_eq BitVec.setWidth_cast

-- This will be resolved once we rejoin `master`.
simp_lc whitelist BitVec.ofFin_add BitVec.add_zero

#guard_msgs (drop info) in
simp_lc check in BitVec
