def areAllSame' (arr : Array Nat) (i : Nat := 0) :=
  if _ : i < arr.size then
    if arr[i] = arr[0] then
      areAllSame' arr (i + 1)
    else
      false
  else
    true
