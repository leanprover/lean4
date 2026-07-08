import Lean.Level

open Lean

#guard Level.zero == Level.zero
#guard Level.zero != mkLevelSucc Level.zero
#guard mkLevelMax (mkLevelSucc Level.zero) Level.zero != mkLevelSucc Level.zero
#guard mkLevelMax (mkLevelSucc Level.zero) Level.zero == mkLevelMax (mkLevelSucc Level.zero) Level.zero
#guard Level.geq (.max (.param `u) (.param `v)) (.imax (.param `u) (.param `v))
