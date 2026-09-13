import Lean.Runtime

/-!
Checks that Lean reports the version of the OpenSSL it is linked against. `find_package(OpenSSL 3)`
sets a floor rather than pinning a major version, so this asserts the floor holds.
-/

/-- info: true -/
#guard_msgs in
#eval System.Platform.isEmscripten || Lean.openSSLVersion >>> 28 >= 3
