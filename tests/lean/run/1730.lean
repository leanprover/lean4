import Lean
set_option trace.Meta.debug true
class W where
  /-- w -/
  w : Unit

class X extends W where
  /-- x -/
  x : Unit

class Y extends W where
  /-- y -/
  y : Unit

class Y' extends Y where
  /-- h -/
  h : Uint

class Z extends X, Y'

open Lean
def test (declName : Name) : CoreM Unit := do
  let some docstr ← findDocString? (← getEnv) declName | throwError "docstring not found"
  IO.println docstr

/-- info: w -/
#guard_msgs in
#eval test ``W.w

/-- info: x -/
#guard_msgs in
#eval test ``X.x

/-- info: y -/
#guard_msgs in
#eval test ``Z.y

/-- info: h -/
#guard_msgs in
#eval test ``Z.h
