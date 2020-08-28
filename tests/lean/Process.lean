open IO.Process

#eval do
  child ← spawn { cmd := "bash", args := #["-c", "echo hi!"] };
  child.wait

#eval do
  child ← spawn { cmd := "bash", args := #["-c", "echo ho!"], stdout := Stdio.piped };
  child.wait;
  child.stdout.readToEnd

#eval do
  child ← spawn { cmd := "bash", args := #["-c", "head -n 1"], stdin := Stdio.piped, stdout := Stdio.piped };
  child.stdin.putStrLn "hu!";
  child.stdin.flush;
  child.wait;
  child.stdout.readToEnd
