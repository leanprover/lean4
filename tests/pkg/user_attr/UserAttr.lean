import UserAttr.Tst
import UserAttr.MetaUser

open Lean

def tst : MetaM Unit := do
  let env ← getEnv
  assert! (blaAttr.hasTag env `f)
  assert! (blaAttr.hasTag env `g)
  assert! !(blaAttr.hasTag env `id)
  pure ()

#eval tst
