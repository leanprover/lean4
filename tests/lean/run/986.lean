attribute [simp] Array.insertionSort.swapLoop

/--
info: Array.insertionSort.swapLoop.eq_1.{u_1} {α : Type u_1} (lt : α → α → Bool) (a : Array α) (h : 0 < Array.size a) :
  Array.insertionSort.swapLoop lt a 0 h = a
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_1

/--
info: Array.insertionSort.swapLoop.eq_2.{u_1} {α : Type u_1} (lt : α → α → Bool) (a : Array α) (j' : Nat)
  (h : Nat.succ j' < Array.size a) :
  Array.insertionSort.swapLoop lt a (Nat.succ j') h =
    let_fun h' := ⋯;
    if lt a[Nat.succ j'] a[j'] = true then Array.insertionSort.swapLoop lt (Array.swap a ⟨Nat.succ j', h⟩ ⟨j', h'⟩) j' ⋯
    else a
-/
#guard_msgs in
#check Array.insertionSort.swapLoop.eq_2
