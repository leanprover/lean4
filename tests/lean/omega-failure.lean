/-!
Testing omega's failure message
-/

example : 0 < 0 := by omega

example (x : Nat) : x < 0 := by omega

example (x : Nat) (y : Int) : x < y := by omega

example (x y : Int) : 5 < x ∧ x < 10 → y > 0 := by omega

-- this used to fail with y = x, but then omega got better, so now there are unrelated x and y
-- to make omega fail
theorem sizeOf_snd_lt_sizeOf_list {α : Type u} {β : Type v} [SizeOf α] [SizeOf β]
  {x y : α × β} {xs : List (α × β)} :
  y ∈ xs → sizeOf x.snd < 1 + sizeOf xs
:= by
  intro h
  have := List.sizeOf_lt_of_mem h
  have : sizeOf x = 1 + sizeOf x.1 + sizeOf x.2 := rfl
  omega


example (reallyreallyreallyreally longlonglonglong namenamename : Nat) :
  reallyreallyreallyreally < longlonglonglong + namenamename := by omega


def a := 1

example (b c d e f g h i j k l m n o p : Nat) :
  b + c + d + e + f + g + h + i + j + k + l + m + n + o + p < 100 := by omega
