#eval Id.run do
  let mut x := 2
  if let n + 1 := x then
    x := n
  return x

#eval Id.run do
  let mut x := 2
  if let 0 := x then
    x := 0
  else if let n + 1 := x then
    x := n
  else
    x := x + 1
  return x

#eval Id.run do
  let mut some x ← pure $ some 2 | 0
  x := x - 1
  pure x

#eval Id.run do
  let mut some x := some 2 | 0
  x := x - 1
  pure x
