import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a policy permitting TLS 1.3 but leaving only `TLS_AES_128_CCM_8_SHA256`, which Lean does
not allow, is refused rather than producing a context whose TLS 1.3 handshakes all fail. A
standalone build reads no configuration and builds it. It must run before the process's first
context, since OpenSSL is initialized once, so it has a file of its own. Windows is skipped: libuv
sets variables there through the Win32 API, which `getenv` does not see.
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
      match ← (discard <| Context.Client.mk { trust := .insecureSkipVerify }).toBaseIO, standalone with
      | .ok _, true => pure ()
      | .error e, true => throw <| IO.userError s!"a standalone build read the policy: {e}"
      -- The code is the platform's `ENOTSUP`, so only the details are compared.
      | .error (.unsupportedOperation _ details), false =>
        unless details == "could not configure the TLS cipher suites: the system OpenSSL \
            configuration permits TLS 1.3 but leaves none of its suites that Lean allows" do
          throw <| IO.userError s!"unexpected failure: {details}"
      | .error e, false => throw <| IO.userError s!"unexpected failure: {e}"
      | .ok _, false =>
        throw <| IO.userError "a context was built with no TLS 1.3 suite while TLS 1.3 is permitted"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
