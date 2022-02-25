def test2 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    i := i + 1
  until i >= 10
  println! "test2 done {i}"

#eval test2

def test3 : IO Unit := do
  let mut i := 0
  repeat
    println! "{i}"
    if i > 10 && i % 3 == 0 then break
    i := i + 1
  println! "test3 done {i}"

#eval test3
