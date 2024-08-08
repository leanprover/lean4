import Lean.Runtime

-- 77824 -> 0x013000 -> 0x01.0x30.0x00 -> 1.48.0
/-- info: 77824 -/
#guard_msgs in
#eval Lean.libUvVersion
