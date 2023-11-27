import Lean.Level

open Lean

#eval
  assert! levelZero == levelZero
  assert! !(levelZero == mkLevelSucc levelZero)
  assert! !(mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelSucc levelZero)
  assert! mkLevelMax (mkLevelSucc levelZero) levelZero == mkLevelMax (mkLevelSucc levelZero) levelZero
  assert! Level.geq (.max (.param `u) (.param `v)) (.imax (.param `u) (.param `v))
  true
