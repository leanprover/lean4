import Lean.Runtime

-- This is the major version of LibUV
/-- info: 1 -/
#guard_msgs in
#eval Lean.libUVVersion >>> 16
