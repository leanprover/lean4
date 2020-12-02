constant getA (s : String) : Array String := #[]

private def resolveLValAux (s : String) (i : Nat) : Nat :=
  let s1 := s
  let as := getA s1
  if h : i < as.size then
    i - 1
  else
    i
