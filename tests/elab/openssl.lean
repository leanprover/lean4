import Lean.Runtime

-- OpenBSD may use LibreSSL; other native platforms require OpenSSL 3.
/-- info: true -/
#guard_msgs in
#eval
  if System.Platform.isEmscripten then
    true
  else
    let major := Lean.openSSLVersion >>> 28
    let isOpenBSD := (System.Platform.target.splitOn "-").any (·.startsWith "openbsd")
    major == 3 || (isOpenBSD && major == 2)
