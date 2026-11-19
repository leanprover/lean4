
open IO.FS
def usingIO {α} (x : IO α) : IO α := x

#eval usingIO do
let out ← IO.getStdout;
out.putStrLn "print stdout"

#eval usingIO do
let err ← IO.getStderr;
(err.putStr "print stderr" : IO Unit)

open IO

def test : IO Unit := do
FS.withFile "stdio.lean.stdout1.txt" IO.FS.Mode.write $ fun h₁ => do
{ let h₂ ← FS.Handle.mk "stdio.lean.stdout2.txt" IO.FS.Mode.write;
  withStdout (Stream.ofHandle h₁) $ do
    println "line 1";
    tryCatch
      ( do
        withStdout (Stream.ofHandle h₂) $ println "line 2";
        throw $ IO.userError "my error" )
      ( fun e => println e );
    println "line 3" };
println "line 4";
println "\n> stdio.lean.stdout1.txt";
readFile "stdio.lean.stdout1.txt" >>= print;
println "\n> stdio.lean.stdout2.txt";
readFile "stdio.lean.stdout2.txt" >>= print

#eval test
