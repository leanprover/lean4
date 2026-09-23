import Std.Internal.SSL
import Std.Async.System

/-!
The TLS 1.3 counterpart of `async_ssl_context_policy.lean`. `OPENSSL_CONF` names a policy whose only
TLS 1.3 suite is `TLS_AES_128_CCM_8_SHA256`, which Lean does not allow, while leaving TLS 1.3 itself
permitted. OpenSSL would then offer TLS 1.3 with no suite to negotiate and fail every handshake, so
a build reading the policy refuses the context instead. A standalone build reads no configuration,
and builds it. This has to run before the first context of the process, because OpenSSL is
initialized once, so it lives in a file of its own. Windows is skipped because libuv sets variables
there through the Win32 API, which the C runtime's `getenv` does not observe.
-/

open Std.Internal.SSL

def ccm8Policy : String :=
  "openssl_conf = openssl_init\n\
   [openssl_init]\n\
   ssl_conf = ssl_sect\n\
   [ssl_sect]\n\
   system_default = system_default_sect\n\
   [system_default_sect]\n\
   Ciphersuites = TLS_AES_128_CCM_8_SHA256\n"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return

  let standalone := (← IO.getEnv "LEAN_STANDALONE") == some "1"

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path ccm8Policy
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      match ← (discard <| Context.Client.mk { verifyPeer := false }).toBaseIO, standalone with
      | .ok _, true => pure ()
      | .error e, true => throw <| IO.userError s!"a standalone build read the policy: {e}"
      | .error e, false =>
        unless toString e == "could not configure the TLS cipher suites: the system OpenSSL \
            configuration permits TLS 1.3 but leaves none of its suites that Lean allows" do
          throw <| IO.userError s!"unexpected failure: {e}"
      | .ok _, false =>
        throw <| IO.userError "a context was built with no TLS 1.3 suite while TLS 1.3 is permitted"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
