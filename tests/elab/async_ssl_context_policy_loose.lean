import Std.Internal.SSL
import Std.Async.System
import Lean

/-!
Checks that a system crypto policy asking for *less* than Lean's floor is overridden, the companion of
`async_ssl_context_policy.lean`. `OPENSSL_CONF` names a policy that drops the security level to 0,
allows TLS 1.0, re-enables unsafe legacy renegotiation, and offers one of Lean's TLS 1.2 suites
beside a static-RSA one. Short of a handshake only the security level is observable here: the shared
suite keeps the context buildable, and a 512-bit certificate is still refused, so level 0 did not
stick. That the configuration is read at all is what `async_ssl_context_config.lean` checks; a
standalone build reads none, and passes the same checks for that reason. This has to run before the
first context of the process, because OpenSSL is initialized once, so it lives in a file of its own.
Windows is skipped because libuv sets variables there through the Win32 API, which the C runtime's
`getenv` does not observe.
-/

open Std.Internal.SSL

open Lean in
elab "include_cert% " path:str : term => do
  let dir := (System.FilePath.mk (← readThe Core.Context).fileName).parent.getD ⟨"."⟩
  return mkStrLit (← IO.FS.readFile (dir / path.getString))

def weakCertPEM : String := include_cert% "async_ssl_certs/weakcert.pem"
def keyPEM : String := include_cert% "async_ssl_certs/key.pem"

def loosePolicy : String :=
  "openssl_conf = openssl_init\n\
   [openssl_init]\n\
   ssl_conf = ssl_sect\n\
   [ssl_sect]\n\
   system_default = system_default_sect\n\
   [system_default_sect]\n\
   MinProtocol = TLSv1\n\
   Options = UnsafeLegacyRenegotiation\n\
   CipherString = ECDHE-RSA-AES128-GCM-SHA256:AES128-SHA:@SECLEVEL=0\n"

def weakCertError : String :=
  "invalid argument (error code: 22, the certificate is rejected by the TLS security level (key too \
    small or signature digest too weak))"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path loosePolicy
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      discard <| Context.Client.mk { verifyPeer := false }

      match ← (discard <| Context.Server.mk { cert := .text weakCertPEM, key := .text keyPEM }).toBaseIO with
      | .ok _ => throw <| IO.userError "a 512-bit certificate was accepted under a level-0 policy"
      | .error e =>
        unless toString e == weakCertError do
          throw <| IO.userError s!"unexpected failure: {e}"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
