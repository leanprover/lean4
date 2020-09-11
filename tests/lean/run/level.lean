import Lean.Level
new_frontend
open Lean

#eval levelZero == levelZero
#eval levelZero == mkLevelSucc levelZero
#eval mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelSucc levelZero
#eval mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelMax (mkLevelSucc levelZero) levelZero
