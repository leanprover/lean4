def sum (as : Array Nat) : Nat :=
  go 0 0
where
  go (i : Nat) (s : Nat) : Nat :=
    if h : i < as.size then
      go (i+1) (s + as.get ⟨i, h⟩)
    else
      s
termination_by' measure (fun ⟨i, s⟩ => as.size - i)
