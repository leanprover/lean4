import Std.Internal.SSL
import Std.Async.System

/-!
Checks that a policy capping the version below TLS 1.2 refuses every context: `OPENSSL_CONF`
names a policy with `MaxProtocol = TLSv1.1`, which leaves no version Lean allows. It must run before the process's first context, since OpenSSL is initialized once, so it has
a file of its own. A standalone build reads no configuration, so there every context builds. Windows
is skipped: libuv sets variables there through the Win32 API, which `getenv` does not see.
-/

open Std.Internal.SSL

def policy : String :=
  "openssl_conf = openssl_init\n\
   [openssl_init]\n\
   ssl_conf = ssl_sect\n\
   [ssl_sect]\n\
   system_default = system_default_sect\n\
   [system_default_sect]\n\
   MaxProtocol = TLSv1.1\n"

-- Runs `act` under `policy`, telling it whether the build reads the policy at all.
def withPolicy (act : Bool → IO Unit) : IO Unit := do
  if System.Platform.isWindows then
    return

  let reads := (← IO.getEnv "LEAN_STANDALONE") != some "1"

  IO.FS.withTempDir fun dir => do
    let path := dir / "openssl.cnf"
    IO.FS.writeFile path policy
    let old ← IO.getEnv "OPENSSL_CONF"
    Std.Async.System.setEnvVar "OPENSSL_CONF" path.toString

    try act reads finally
      match old with
      | some v => Std.Async.System.setEnvVar "OPENSSL_CONF" v
      | none => Std.Async.System.unsetEnvVar "OPENSSL_CONF"

-- Expects `act` to be refused as `unsupportedOperation` with `details` when the policy is read.
def expectRefused (reads : Bool) (details : String) (act : IO Unit) : IO Unit := do
  match ← act.toBaseIO, reads with
  | .ok _, false => pure ()
  | .error e, false => throw <| IO.userError s!"a build not reading the policy failed: {e}"
  -- The code is the platform's `ENOTSUP`, so only the details are compared.
  | .error (.unsupportedOperation _ d), true =>
    unless d == details do
      throw <| IO.userError s!"unexpected failure: {d}"
  | .error e, true => throw <| IO.userError s!"unexpected failure: {e}"
  | .ok _, true => throw <| IO.userError s!"accepted despite the policy: expected {details}"

#eval withPolicy fun reads =>
  expectRefused reads "could not configure the TLS versions: the system OpenSSL configuration \
      permits none of the TLS versions allowed here"
    (discard <| Context.Client.mk { trust := .insecureSkipVerify })
