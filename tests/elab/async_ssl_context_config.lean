import Std.Internal.SSL
import Std.Async.System

/-!
Checks that building a TLS context never loads an OpenSSL configuration file. A release toolchain's
compiled-in configuration path names a directory on the machine it was built on, which on the machine
it runs on can belong to anyone; a file planted there could load a provider module or lower the
security level of every context. `OPENSSL_CONF` stands in for that file here: it names a
configuration whose provider section replaces the default provider with one that cannot be loaded,
so a context built after reading it has no ciphers and cannot be created. It has to be set before the
first context of the process, because OpenSSL is initialized once, so this lives in a file of its own.
Windows is skipped because libuv sets variables there through the Win32 API, which the C runtime's
`getenv` does not observe.
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

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path brokenConfig
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try
      let _clientCtx ← Context.Client.mk { verifyPeer := false }
    finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"
