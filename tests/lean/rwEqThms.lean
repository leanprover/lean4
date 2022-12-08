example {a : α} {as bs : List α} (h : bs = a::as) : as.length + 1 = bs.length := by
  rw [← List.length]
  trace_state -- lhs was folded
  rw [h]

example {a : α} {as bs : List α} (h : as = bs) : (a::b::as).length = bs.length + 2 := by
  rw [List.length, List.length]
  trace_state -- lhs was unfolded
  rw [h]

example {a : α} {as bs : List α} (h : as = bs) : (a::b::as).length = (b::bs).length + 1 := by
  conv => lhs; rw [List.length, List.length]
  trace_state -- lhs was unfolded
  conv => rhs; rw [List.length]
  trace_state -- rhs was unfolded
  rw [h]

example {a : α} {as bs : List α} (h : as = bs) : id (id ((a::b::as).length)) = (b::bs).length + 1 := by
  rw [id]
  trace_state
  rw [id]
  trace_state
  rw [List.length, List.length, List.length]
  trace_state
  rw [h]
