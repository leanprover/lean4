import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a system crypto policy can narrow the TLS settings of a context but never widen them. A
build linking the system's OpenSSL reads the distribution's configuration, whose `system_default`
section is applied as each context is created, before Lean sets its own floor. Lean's floor has to
intersect with that policy rather than replace it.

`OPENSSL_CONF` names a policy here whose only TLS 1.2 suite is static-RSA `AES128-SHA`, at security
level 0. It shares no suite with Lean's, so a context built after reading it has none left and is
refused; replacing the policy with Lean's own list would instead build it. A standalone build reads no
configuration at all, so it builds the context either way. This has to run before the first context
of the process, because OpenSSL is initialized once, so it lives in a file of its own. Windows is
skipped because libuv sets variables there through the Win32 API, which the C runtime's `getenv`
does not observe.
-/

open Std.Internal.SSL

def disjointPolicy : String :=
  "openssl_conf = openssl_init\n\
   [openssl_init]\n\
   ssl_conf = ssl_sect\n\
   [ssl_sect]\n\
   system_default = system_default_sect\n\
   [system_default_sect]\n\
   MinProtocol = TLSv1\n\
   CipherString = AES128-SHA:@SECLEVEL=0\n"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return

  let standalone := (← IO.getEnv "LEAN_STANDALONE") == some "1"

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path disjointPolicy
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      match ← (discard <| Context.Client.mk { verifyPeer := false }).toBaseIO, standalone with
      | .ok _, true => pure ()
      | .error e, true => throw <| IO.userError s!"a standalone build read the policy: {e}"
      | .error e, false =>
        unless toString e == "could not configure the TLS cipher suites: the system OpenSSL \
            configuration permits TLS 1.2 but leaves none of its suites that Lean allows" do
          throw <| IO.userError s!"unexpected failure: {e}"
      | .ok _, false =>
        throw <| IO.userError "the policy's cipher suites were replaced rather than narrowed"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
