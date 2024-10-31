import Lean.SimpLC.Whitelists.Root

simp_lc ignore Prod.exists
simp_lc ignore Prod.forall

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Prod _root_
