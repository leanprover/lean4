--
open IO.Process

def usingIO {α} (x : IO α) : IO α := x

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "exit 1"] };
  child.wait

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "echo hi!"] };
  child.wait

#eval usingIO do
  let child ← spawn { cmd := "sh", args := #["-c", "echo ho!"], stdout := Stdio.piped };
  discard $ child.wait;
  child.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "head", args := #["-n1"], stdin := Stdio.piped, stdout := Stdio.piped };
  child.stdin.putStrLn "hu!";
  child.stdin.flush;
  discard $ child.wait;
  child.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "true", stdin := Stdio.piped };
  discard $ child.wait;
  child.stdin.putStrLn "ha!";
  child.stdin.flush <|> IO.println "flush of broken pipe failed"

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
  }
  let (stdin, lean) ← lean.takeStdin
  stdin.putStr "#exit\n"
  lean.wait
