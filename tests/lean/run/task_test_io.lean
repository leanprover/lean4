#eval do
  t1 ← IO.mapTask IO.println (Task.mk fun _ => "ha");
  pure ()

#eval do
  t1 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "hi";
  t2 ← IO.asTask $ Nat.forM 10 fun _ => IO.println "ho";
  IO.ofExcept t1.get
