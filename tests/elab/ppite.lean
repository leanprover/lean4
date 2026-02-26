def f (xs : List Nat) : IO Unit := do
  xs.forM fun x =>
    if x == 0 then do
      IO.println "foo"
      IO.println "zero"
    else if x % 2 == 0 then do
      IO.println x
      IO.println "even"
    else do
      IO.println x
      IO.println "odd"

#print f

#check if true then 1 else 0

#check if h : true then 1 else 0
