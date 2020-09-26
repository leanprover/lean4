new_frontend
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
  child.wait;
  child.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "head", args := #["-n1"], stdin := Stdio.piped, stdout := Stdio.piped };
  child.stdin.putStrLn "hu!";
  child.stdin.flush;
  child.wait;
  child.stdout.readToEnd

#eval usingIO do
  let child ← spawn { cmd := "true", stdin := Stdio.piped };
  child.wait;
  child.stdin.putStrLn "ha!";
  child.stdin.flush <|> IO.println "flush of broken pipe failed"

#eval usingIO do
  -- produce enough output to fill both pipes on all platforms
  let out ← output { cmd := "sh", args := #["-c", "printf '%100000s' >& 2; printf '%100001s'"] };
  IO.println out.stdout.length;
  IO.println out.stderr.length
