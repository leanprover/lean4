attribute [simp] Array.insertionSort.swapLoop

/--
info: Array.insertionSort.swapLoop.eq_1.{u_1} {α : Type u_1} (lt : α → α → Bool) (a : Array α) (h : 0 < a.size) :
  Array.insertionSort.swapLoop lt a 0 h = a
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_1

/--
info: Array.insertionSort.swapLoop.eq_2.{u_1} {α : Type u_1} (lt : α → α → Bool) (a : Array α) (j' : Nat)
  (h : j'.succ < a.size) :
  Array.insertionSort.swapLoop lt a j'.succ h =
    if lt a[j'.succ] a[j'] = true then Array.insertionSort.swapLoop lt (a.swap ⟨j'.succ, h⟩ ⟨j', ⋯⟩) j' ⋯ else a
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_2
