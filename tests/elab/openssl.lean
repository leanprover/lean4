import Lean.Runtime

/-!
Checks that Lean is linked against OpenSSL 3 or newer, the minimum required by `src/CMakeLists.txt`.
-/

-- Non-emscripten build: expect OpenSSL 3 or newer
/-- info: true -/
#guard_msgs in
#eval if !System.Platform.isEmscripten then decide (Lean.openSSLVersion >>> 28 ≥ 3) else true
