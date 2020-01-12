
#eval do
out ← IO.getStdout;
(out.putStrLn "print stdout" : IO Unit)

#eval do
err ← IO.getStderr;
(err.putStr "print stderr" : IO Unit)

open IO

def test : IO Unit := do
FS.withFile "stdout1.txt" IO.FS.Mode.write $ fun h₁ => do
{ h₂ ← FS.Handle.mk "stdout2.txt" IO.FS.Mode.write;
  withStdout h₁ $ do
    println "line 1";
    catch
    ( do
      withStdout h₂ $ println "line 2";
      throw $ IO.userError "my error" )
    ( fun e => println e );
    println "line 3" };
println "line 4";
println "\n> stdout1.txt";
readFile "stdout1.txt" >>= print;
println "\n> stdout2.txt";
readFile "stdout2.txt" >>= print

#eval test
