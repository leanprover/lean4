import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a system crypto policy can narrow Lean's TLS settings but not widen them. `OPENSSL_CONF`
names a policy whose only TLS 1.2 suite is static-RSA `AES128-SHA`, which Lean does not allow, so a
build reading it refuses the context; a standalone build reads no configuration and builds it. It
must run before the process's first context, since OpenSSL is initialized once, so it has a file of
its own. Windows is skipped: libuv sets variables there through the Win32 API, which `getenv` does
not see.
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
      -- The code is the platform's `ENOTSUP`, so only the details are compared.
      | .error (.unsupportedOperation _ details), false =>
        unless details == "could not configure the TLS cipher suites: the system OpenSSL \
            configuration permits TLS 1.2 but leaves none of its suites that Lean allows" do
          throw <| IO.userError s!"unexpected failure: {details}"
      | .error e, false => throw <| IO.userError s!"unexpected failure: {e}"
      | .ok _, false =>
        throw <| IO.userError "the policy's cipher suites were replaced rather than narrowed"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
