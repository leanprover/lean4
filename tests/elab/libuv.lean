import Lean.Runtime

/-!
Checks that Lean is linked against libuv 1.x, or against none on Emscripten, which reports
version 0. The minimum version bundled into releases is checked in CI instead.
-/

-- Non-emscripten build: expect the major version of LibUV
/-- info: 1 -/
#guard_msgs in
#eval if !System.Platform.isEmscripten then Lean.libUVVersion >>> 16 else 1

-- Emscripten build: expect 0
/-- info: 0 -/
#guard_msgs in
#eval if System.Platform.isEmscripten then Lean.libUVVersion >>> 16 else 0
