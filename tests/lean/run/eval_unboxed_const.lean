import Lean


open Lean

def c1 : Bool := true

unsafe def tst1 : CoreM Unit := do
let env ← getEnv;
let v := env.evalConst Bool {} `c1;
IO.println v

/-- info: ok: true -/
#guard_msgs in
#eval tst1 -- used to output incorrect value (ok false). Reason: the unboxed value `true` is `1`, but the boxed `false` value is also `1`.

def c2 : Bool := false

unsafe def tst2 : CoreM Unit := do
let env ← getEnv;
let v := env.evalConst Bool {} `c2;
IO.println v

/-- info: ok: false -/
#guard_msgs in
#eval tst2 -- used to crash since `0` is not a valid boxed value
