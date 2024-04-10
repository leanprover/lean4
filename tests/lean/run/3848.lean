theorem sizeOf_snd_lt_sizeOf_list
  {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {x : α × β} {xs : List (α × β)} :
  x ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  have h1 := List.sizeOf_lt_of_mem h
  have h2 : sizeOf x = 1 + sizeOf x.1 + sizeOf x.2 := rfl
  cases x; dsimp at *
  omega
