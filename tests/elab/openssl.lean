import Lean.Runtime

-- Non-emscripten build: expect the major version of OpenSSL (3)
/-- info: 3 -/
#guard_msgs in
#eval if !System.Platform.isEmscripten then Lean.openSSLVersion >>> 28 else 3
