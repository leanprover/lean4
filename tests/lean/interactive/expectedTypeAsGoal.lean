def big : IO Unit := do
  let x := 10
  if true then
    IO.println s!"a{x}"
   --^ $/lean/plainTermGoal
  if false then
    IO.println "b"
  if 1 < 3 then
    IO.println "c"
