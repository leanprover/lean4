#eval show Nat from do
  let mut x := 2
  if let n + 1 := x then
    x := n
  return x

#eval show Nat from do
  let mut x := 2
  if let 0 := x then
    x := 0
  else if let n + 1 := x then
    x := n
  else
    x := x + 1
  return x
