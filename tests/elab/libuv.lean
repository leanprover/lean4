import Lean.Runtime

-- Non-emscripten build: expect the major version of LibUV
/-- info: 1 -/
#guard_msgs in
#eval if !System.Platform.isEmscripten then Lean.libUVVersion >>> 16 else 1

-- Emscripten build: expect 0
/-- info: 0 -/
#guard_msgs in
#eval if System.Platform.isEmscripten then Lean.libUVVersion >>> 16 else 0
