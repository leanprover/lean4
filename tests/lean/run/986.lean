attribute [simp] Array.insertionSort.swapLoop

/--
info: Array.insertionSort.swapLoop.eq_1.{u_1} {α : Type u_1} (lt : α → α → Bool) (xs : Array α) (h : 0 < xs.size) :
  Array.insertionSort.swapLoop lt xs 0 h = xs
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_1

/--
info: Array.insertionSort.swapLoop.eq_2.{u_1} {α : Type u_1} (lt : α → α → Bool) (xs : Array α) (j' : Nat)
  (h : j'.succ < xs.size) :
  Array.insertionSort.swapLoop lt xs j'.succ h =
    if lt xs[j'.succ] xs[j'] = true then Array.insertionSort.swapLoop lt (xs.swap j'.succ j' h ⋯) j' ⋯ else xs
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_2
