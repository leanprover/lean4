import Lean.Level

open Lean

#guard Level.zero == Level.zero
#guard Level.zero != mkLevelSucc Level.zero
#guard mkLevelMax (mkLevelSucc Level.zero) Level.zero != mkLevelSucc Level.zero
#guard mkLevelMax (mkLevelSucc Level.zero) Level.zero == mkLevelMax (mkLevelSucc Level.zero) Level.zero
#guard Level.geq (.max (.param `u) (.param `v)) (.imax (.param `u) (.param `v))

-- `mkLevelIMax' 1 u = u` (matches C++ `mk_imax`'s `is_one(l1)` case).
#guard mkLevelIMax' (mkLevelSucc Level.zero) (Level.param `u) == Level.param `u

-- `max (succ u) 1 = succ u` under the `subsumes` rule.
#guard mkLevelMax' (mkLevelSucc (Level.param `u)) (mkLevelSucc Level.zero) == mkLevelSucc (Level.param `u)
