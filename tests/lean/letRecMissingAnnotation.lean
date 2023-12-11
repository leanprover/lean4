def sum (as : Array Nat) : Nat :=
  let rec go (i : Nat) (s : Nat) : Nat :=
    if h : i < as.size then
      go (i+2) (s + as.get ⟨i, h⟩) -- Error
    else
      s
    termination_by i _ => as.size - i
  go 0 0
