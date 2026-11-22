/-!
Functional induction for structural recursion through a `match (generalizing := false)`, as in
`Array.insertionSort.swapLoop`: the goal cannot be refined by the match (as `h` mentions `j`),
but the induction hypothesis still has to be.
-/

def swapLoop (xs : Array Nat) (j : Nat) (h : j < xs.size) : Array Nat :=
  match (generalizing := false) he:j with
  | 0    => xs
  | j'+1 =>
    have h' : j' < xs.size := by subst j; exact Nat.lt_trans (Nat.lt_succ_self _) h
    swapLoop xs j' h'
termination_by structural j

/--
info: swapLoop.induct (xs : Array Nat) (motive : (j : Nat) → j < xs.size → Prop) (case1 : ∀ (h : 0 < xs.size), motive 0 h)
  (case2 : ∀ (j' : Nat) (h : j'.succ < xs.size) (h' : j' < xs.size), motive j' h' → motive j'.succ h) (j : Nat)
  (h : j < xs.size) : motive j h
-/
#guard_msgs in
#check swapLoop.induct

/--
info: swapLoop.induct_unfolding (xs : Array Nat) (motive : (j : Nat) → j < xs.size → Array Nat → Prop)
  (case1 : ∀ (h : 0 < xs.size), motive 0 h xs)
  (case2 :
    ∀ (j' : Nat) (h : j'.succ < xs.size) (h' : j' < xs.size),
      motive j' h' (swapLoop xs j' h') → motive j'.succ h (swapLoop xs j' h'))
  (j : Nat) (h : j < xs.size) : motive j h (swapLoop xs j h)
-/
#guard_msgs in
#check swapLoop.induct_unfolding
