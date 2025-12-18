import Lean.Level

open Lean

#guard levelZero == levelZero
#guard levelZero != mkLevelSucc levelZero
#guard mkLevelMax (mkLevelSucc levelZero) levelZero != mkLevelSucc levelZero
#guard mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelMax (mkLevelSucc levelZero) levelZero
#guard Level.geq (.max (.param `u) (.param `v)) (.imax (.param `u) (.param `v))
