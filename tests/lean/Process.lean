--
open IO.Process

def usingIO {α} (x : IO α) : IO α := x

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "exit 1"] };
  child.wait

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "echo ho!"], stdout := Stdio.piped };
  child.wait >>= IO.println;
  child.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "head", args := #["-n1"], stdin := Stdio.piped, stdout := Stdio.piped };
  child.stdin.putStrLn "hu!";
  child.stdin.flush;
  discard $ child.wait;
  child.stdout.readToEnd

#eval usingIO do
  -- produce enough output to fill both pipes on all platforms
  let out ← output { cmd := "sh", args := #["-c", "printf '%100000s' >& 2; printf '%100001s'"] };
  IO.println out.stdout.length;
  IO.println out.stderr.length

#eval usingIO do
  -- With a non-empty stdin, cat would wait on input forever
  let child ← spawn { cmd := "sh", args := #["-c", "cat"], stdin := Stdio.null };
  child.wait

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "echo nullStdout"], stdout := Stdio.null };
  child.wait

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "echo nullStderr >& 2"], stderr := Stdio.null };
  child.wait

#eval usingIO do
  let lean ← IO.Process.spawn {
    cmd := "lean",
    args := #["--stdin"]
    stdin := IO.Process.Stdio.piped
    stdout := IO.Process.Stdio.piped
  }
  let (stdin, lean) ← lean.takeStdin
  stdin.putStr "#exit\n"
  let _ ← lean.wait
  lean.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "cat"], stdin := .piped, stdout := .piped }
  IO.println (← child.tryWait)
  -- We take stdin in here such that it is closed automatically by dropping the object right away.
  -- This will kill the `cat` process.
  let (stdin, child) ← child.takeStdin
  IO.sleep 1000
  child.tryWait
