import Lean.Runtime

/-!
Checks that Lean is compiled against OpenSSL 3 or newer, the minimum required by `src/CMakeLists.txt`,
and that the headers it is compiled against have the same major version as the library it is linked
against.
-/

-- Non-emscripten build: expect OpenSSL 3 or newer
/-- info: true -/
#guard_msgs in
#eval if !System.Platform.isEmscripten then decide (Lean.openSSLVersion >>> 28 ≥ 3) else true

/-- info: true -/
#guard_msgs in
#eval Lean.openSSLVersion >>> 28 == Lean.openSSLLinkedVersion >>> 28
