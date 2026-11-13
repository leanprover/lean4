/-!
A Lean program that is started with closed standard streams sees the null device in their place:
writing to them succeeds, reading from standard input reaches the end of the file, and child
processes inherit usable streams. Otherwise the descriptors that the runtime opens for itself would
take the place of the closed streams.

Windows has no closed standard streams of this kind, so the test does nothing there.
-/

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-- Uses each standard stream, and has a child process do so too, reporting to the file `args[0]`. -/
def source : String := "
def attempt (act : IO Unit) : IO String := do
  match ← act.toBaseIO with
  | .ok () => return \"ok\"
  | .error e => return toString e

def main (args : List String) : IO Unit := do
  let stdout ← attempt do
    let h ← IO.getStdout
    h.putStrLn \"to stdout\"
    h.flush
  let stderr ← attempt do
    let h ← IO.getStderr
    h.putStrLn \"to stderr\"
    h.flush
  let stdin ← attempt do
    let line ← (← IO.getStdin).getLine
    unless line.isEmpty do throw <| IO.userError s!\"read {line.quote}\"
  let child ← IO.Process.spawn { cmd := \"sh\", args := #[\"-c\", \"echo out && echo err >&2 && cat\"] }
  let code ← child.wait
  IO.FS.writeFile args[0]! s!\"stdout: {stdout}, stderr: {stderr}, stdin: {stdin}, child: {code}\"
"

#eval show IO Unit from do
  if System.Platform.isWindows then return
  IO.FS.withTempDir fun dir => do
    let file := dir / "main.lean"
    let report := dir / "report"
    IO.FS.writeFile file source
    -- What the program and its child write to standard output when it is open.
    let childOut := "to stdout\nout\n".toUTF8
    for (closed, expected) in [("<&-", childOut), (">&-", .empty), ("2>&-", childOut),
        ("<&- >&- 2>&-", .empty)] do
      let out ← IO.Process.binOutput {
        cmd := "sh"
        args := #["-c", s!"exec \"$@\" {closed}", "sh", (← IO.appPath).toString, "--run",
          file.toString, report.toString] }
      let describe (bytes : ByteArray) : String :=
        match String.fromUTF8? bytes with
        | some s => s.quote
        | none => s!"non-UTF-8 bytes {(bytes.extract 0 256).toList} of {bytes.size}"
      let details := s!"exit code {out.exitCode}, stdout {describe out.stdout}, stderr {describe out.stderr}"
      check (out.exitCode == 0 && out.stdout == expected) s!"{closed}: {details}"
      let result ← IO.FS.readFile report
      check (result == "stdout: ok, stderr: ok, stdin: ok, child: 0") s!"{closed}: {result}; {details}"
      IO.FS.removeFile report
