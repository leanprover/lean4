def numChars (s : String) : Nat :=
  go s.iter
where
  go (i : String.Iterator) : Nat :=
    if h : i.hasNext then
      go i.next + 1
    else
      0

#eval numChars "aαc"

example : numChars "aαc" = 3 := by
  rfl'

def numChars2 (s : String) : Nat :=
  go s.iter
where
  go (i : String.Iterator) : Nat :=
    match h : i.hasNext with
    | true  => go i.next + 1
    | false => 0

example : numChars2 "aαc" = 3 := by
  rfl'
