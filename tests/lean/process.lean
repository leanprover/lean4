
def prepareTestFile : IO Unit :=
IO.FS.withFile "ex.txt" IO.FS.Mode.write $ fun h => do
  h.putStrLn "line 31";
  h.putStrLn "line 37"

def test1 : IO Unit := do
ch ← IO.Proc.spawn { cmd := "pwd", stdout := IO.Proc.Stdio.piped false };
some out ← pure ch.stdout;
IO.println "> output";
out.readToEnd >>= IO.println

def test2 : IO Unit := do
cd ← IO.Proc.spawn { cmd := "pwd" };
IO.Proc.wait cd;
pure ()

def test3 : IO Unit := do
IO.println "part a";
ch ← IO.Proc.spawn
    { cmd := "cat", args := #["-", "ex.txt"],
      stdin := IO.Proc.Stdio.piped false,
      stdout := IO.Proc.Stdio.piped false,
      };
let pid := ch.pid;
some input ← pure ch.stdin;
some out ← pure ch.stdout;
input.putStrLn "line 1";
input.putStrLn "line 2";
input.putStrLn "line 3";
IO.println "> pause to print ";
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
input.putStrLn "line 4";
input.putStrLn "line 5";
input.putStrLn "line 6";
IO.println "> pause to print ";
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
IO.println "> wait";
IO.Proc.Prim.wait pid;
out.isEof >>= IO.println;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.isEof >>= IO.println;
ln ← out.getLine;
IO.println $ repr ln;
out.isEof >>= IO.println;
-- input.putStrLn "line 6";
pure ()

def test3' : IO Unit := do
IO.println "part b";
ch ← IO.Proc.spawn
    { cmd := "cat", args := #["-","ex.txt"],
      stdin := IO.Proc.Stdio.piped false,
      stdout := IO.Proc.Stdio.piped false,
      };
let pid := ch.pid;
some input ← pure ch.stdin;
some out ← pure ch.stdout;
input.putStrLn "line 1";
out.readToEnd >>= IO.println;
pure ()

def test3'' : IO Unit := do
IO.println "part c";
ch ← IO.Proc.spawn
    { cmd := "cat", args := #["ex.txt","-","ex.txt"],
      stdin := IO.Proc.Stdio.piped false,
      stdout := IO.Proc.Stdio.piped false,
      };
let pid := ch.pid;
some input ← pure ch.stdin;
some out ← pure ch.stdout;
input.putStrLn "line 1";
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.getLine >>= IO.print;
out.isEof >>= IO.println;
out.getLine >>= IO.print;
out.isEof >>= IO.println;
IO.Proc.Prim.wait pid;
pure ()

def test4 : IO Unit := do
cd ← IO.Proc.spawn
  { cmd := "printenv", args := #["PI"],
    env := #[("PI", some "3.14159265")]
    };
IO.Proc.wait cd;
pure ()

def test5 : IO Unit := do
cd ← IO.Proc.spawn { cmd := "pwd", cwd := some ".." };
IO.Proc.wait cd;
pure ()

def test6 : IO Unit := do
cd ← IO.Proc.spawn { cmd := "echo", args := #["foo", "bar"] };
IO.Proc.wait cd;
pure ()

#eval do
prepareTestFile;
IO.println "> test 1 <";
test1;
IO.println "> test 2 <";
test2;
IO.println "> test 3 <";
test3;
test3';
test3'';
IO.println "> test 4 <";
test4;
IO.println "> test 5 <";
test5
