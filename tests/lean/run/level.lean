import Lean.Level

open Lean

#eval levelZero == levelZero
#eval levelZero == mkLevelSucc levelZero
#eval mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelSucc levelZero
#eval mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelMax (mkLevelSucc levelZero) levelZero
