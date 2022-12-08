def sum (as : Array Nat) : Nat :=
  let rec go (i : Nat) (s : Nat) : Nat :=
    if h : i < as.size then
      go (i+2) (s + as.get ⟨i, h⟩) -- Error
    else
      s
  go 0 0
termination_by' measure (fun ⟨i, _⟩ => as.size - i)
