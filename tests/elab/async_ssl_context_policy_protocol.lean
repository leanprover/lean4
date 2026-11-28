import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a policy disabling TLS 1.3 through `Protocol = -TLSv1.3` is not required to leave a TLS
1.3 suite: `OPENSSL_CONF` names such a policy with no TLS 1.3 suites, and the context must still
build. It must run before the process's first context, since OpenSSL is initialized once, so it has
a file of its own. Windows is skipped: libuv sets variables there through the Win32 API, which
`getenv` does not see.
-/

open Std.Internal.SSL

def tls12OnlyPolicy : String :=
  "openssl_conf = openssl_init\n\
   [openssl_init]\n\
   ssl_conf = ssl_sect\n\
   [ssl_sect]\n\
   system_default = system_default_sect\n\
   [system_default_sect]\n\
   Protocol = ALL, -TLSv1.3\n\
   Ciphersuites =\n"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path tls12OnlyPolicy
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      discard <| Context.Client.mk { trust := .insecureSkipVerify }
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
