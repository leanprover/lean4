import Std.Internal.SSL
import Std.Async.System

/-!
Checks which OpenSSL configuration file a TLS context reads, which follows who owns the OpenSSL being
linked. A toolchain bundling its own carries that build's compiled-in configuration path, which names
a directory on the machine it was built on; on the machine it runs on that directory can belong to
anyone, and a file planted there could load a provider module or lower the security level of every
context, so such a build reads no configuration at all. Against a system OpenSSL the same file is the
distribution's own, carrying its crypto policy and FIPS settings, and is read as by any other
consumer of that library.

`OPENSSL_CONF` stands in for that file here: it names a configuration whose provider section replaces
the default provider with one that cannot be loaded, so a context built after reading it has no
ciphers and cannot be created. Whether the context builds is therefore exactly whether the
configuration was read. It has to be set before the first context of the process, because OpenSSL is
initialized once, so this lives in a file of its own. Windows is skipped because libuv sets variables
there through the Win32 API, which the C runtime's `getenv` does not observe.
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

  -- Set by the test environment for a build bundling its own dependencies, which is the build whose
  -- compiled-in configuration path is not to be trusted.
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
