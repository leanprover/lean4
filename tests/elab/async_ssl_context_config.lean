import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a standalone build never reads `openssl.cnf` and a build against the system OpenSSL
does. `OPENSSL_CONF` names a configuration that loads a nonexistent provider, so the context builds
exactly when the file was not read. It must run before the process's first context, since OpenSSL is
initialized once, so it has a file of its own. Windows is skipped: libuv sets variables there
through the Win32 API, which `getenv` does not see.
-/

open Std.Internal.SSL

def brokenConfig : String :=
  "config_diagnostics = 1\n\
   openssl_conf = openssl_init\n\
   [openssl_init]\n\
   providers = provider_sect\n\
   [provider_sect]\n\
   planted = planted_sect\n\
   [planted_sect]\n\
   module = /nonexistent/planted-provider.so\n\
   activate = 1\n"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return

  -- Set by the test environment for a build bundling its own dependencies.
  let standalone := (← IO.getEnv "LEAN_STANDALONE") == some "1"

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path brokenConfig
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      match ← (discard <| Context.Client.mk { verifyPeer := false }).toBaseIO, standalone with
      | .ok _, true => pure ()
      | .error e, true =>
        throw <| IO.userError s!"the planted configuration was read by a standalone build: {e}"
      | .error e, false =>
        unless (toString e).startsWith "could not create the TLS context: library has no ciphers" do
          throw <| IO.userError s!"unexpected failure: {e}"
      | .ok _, false =>
        throw <| IO.userError "the configuration was not read by a build linking the system OpenSSL"
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
