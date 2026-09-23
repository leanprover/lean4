import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a system crypto policy switching a TLS version off with `Protocol` is not held to having
suites for it. `OPENSSL_CONF` names a policy that disables TLS 1.3 through `Protocol = -TLSv1.3` and
lists no TLS 1.3 suite at all, leaving TLS 1.2 with Lean's own suites: a working configuration, so
the context has to build, as it does when the same policy caps the version with `MaxProtocol`. A
standalone build reads no configuration, and builds it too. This has to run before the first context
of the process, because OpenSSL is initialized once, so it lives in a file of its own. Windows is
skipped because libuv sets variables there through the Win32 API, which the C runtime's `getenv`
does not observe.
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
      discard <| Context.Client.mk { verifyPeer := false }
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
