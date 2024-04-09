/-!
Testing omega's failure message
-/

example : 0 < 0 := by omega

example (x : Nat) : x < 0 := by omega

example (x : Nat) (y : Int) : x < y := by omega

example (x y : Int) : 5 < x ∧ x < 10 → y > 0 := by omega

theorem sizeOf_snd_lt_sizeOf_list {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] {x : α × β} {xs : List (α × β)} :
  x ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x = 1 + sizeOf x.1 + sizeOf x.2 := rfl
  omega
