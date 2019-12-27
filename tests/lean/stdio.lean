
#eval do
out ← IO.getStdout;
err ← IO.getStderr;
out.putStr "print stdout";
(err.putStrLn "print stderr" : IO Unit)
