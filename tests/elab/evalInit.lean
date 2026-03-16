#eval show IO _ from do
  return RandomGen.next (← IO.stdGenRef.get) |>.fst
