/-!
`IO.getEnv` must not find a variable for a name that contains `=` or is empty, yet the C library's
`getenv` can match such a name to another variable. macOS compares only up to the first `=`, so
`"HOME=junk"` finds `HOME`, and a name that starts with `=` (or is empty) finds any environment
entry that starts with `=`. glibc returns `b` for `"X=a"` when `X` is `a=b`, so the ordinary
variable the test plants has a value containing `=`. `setenv` cannot create an entry that starts
with `=`, so Python's `execve` plants both in a child `lean` process that runs the lookups.
-/

def childSource : String := r#"
#eval show IO Unit from do
  unless (← IO.getEnv "LEAN_GETENV_EQ") == some "value=x" do
    IO.println "LEAN_GETENV_EQ was not planted"
  for name in ["LEAN_GETENV_EQ=junk", "LEAN_GETENV_EQ=", "LEAN_GETENV_EQ=value",
               "", "=", "=C:", "=HOME", "=LEAN_GETENV_HIDDEN"] do
    if let some v ← IO.getEnv name then
      IO.println s!"getEnv {repr name} returned {repr v}"
"#

def plant : String :=
  "import os, sys; env = dict(os.environ); env['LEAN_GETENV_EQ'] = 'value=x';" ++
  "env['=LEAN_GETENV_HIDDEN'] = 'secret'; os.execve(sys.argv[1], sys.argv[1:], env)"

#eval show IO Unit from do
  if System.Platform.isWindows then
    return
  IO.FS.withTempDir fun dir => do
    let child := dir / "child.lean"
    IO.FS.writeFile child childSource
    let out ← IO.Process.output {
      cmd := "python3"
      args := #["-I", "-c", plant, (← IO.appPath).toString, child.toString]
    }
    unless out.exitCode == 0 && out.stdout.isEmpty do
      throw <| IO.userError s!"child exited with {out.exitCode}:\n{out.stdout}{out.stderr}"
