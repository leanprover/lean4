import Lake.Build.Monad

partial def busyWaitFile (file : System.FilePath) : BaseIO PUnit := do
  if (← file.pathExists) then
    IO.sleep (ms := 300)
    busyWaitFile file

#eval busyWaitFile <| "build" / Lake.lockFileName
