def g (xs : Array Nat) (ys : Array Nat) : IO Unit := do
  let mut s := Std.toStream ys
  for x in xs do
    match Stream.next? s with
    | none => break
    | some (y, s') =>
      s := s'
      IO.println s!"x: {x}, y: {y}"

#eval g #[1, 2, 3] #[4, 5]
#print "-----"

def f [Std.Stream ρ α] [ToString α] (xs : Array Nat) (ys : ρ) : IO Unit := do
  let mut ys := ys
  for x in xs do
    match Std.Stream.next? ys with
    | none => break
    | some (y, ys') =>
      ys := ys'
      IO.println s!"x: {x}, y: {y}"

#eval f #[1, 2, 3] (Std.toStream #[4, 5])
#print "-----"
#eval f #[1, 2] (Std.toStream [4, 5, 6])
#print "-----"
#eval f #[1, 2, 3] (Std.toStream "hello")

def h [Std.Stream ρ α] [ToString α] (s : ρ) : IO Unit := do
  for a in s do
    IO.println a

#eval h (Std.toStream [1, 2, 3])
#print "-----"
#eval h [1, 2, 3]
#print "-----"
#eval h (Std.toStream #[1, 2, 3])
#print "-----"
#eval h #[1, 2, 3, 4, 5, 6, 7][2:5]
#print "-----"
#eval h ([1, 2, 3], [4, 5, 6])
