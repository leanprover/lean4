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

-- Like `Vector.mapFinIdxM.map`: `ys` mentions the discriminant `i`, so neither `i` nor `inv`
-- (whose type mentions `i`) can be abstracted in the goal.
def mapFinIdxM' {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (xs : Vector α n) (f : (i : Nat) → α → (h : i < n) → m β) : m (Vector β n) :=
  let rec map (i : Nat) (j : Nat) (inv : i + j = n) (ys : Vector β (n - i)) : m (Vector β n) := do
    match i, inv with
    | 0,   inv => return ys.cast (by omega)
    | i+1, inv =>
      have j_lt : j < n := by omega
      have : i + (j + 1) = n := by omega
      map i (j+1) this ((ys.push (← f j xs[j] j_lt)).cast (by omega))
  map n 0 rfl (#v[].cast (by simp))

/--
info: mapFinIdxM'.map.induct.{v} {n : Nat} {β : Type v} (motive : (i j : Nat) → i + j = n → Vector β (n - i) → Prop)
  (case1 : ∀ (j : Nat), 0 + j = n → ∀ (inv : 0 + j = n) (ys : Vector β (n - 0)), motive 0 j inv ys)
  (case2 :
    ∀ (j i : Nat) (inv : i + 1 + j = n) (inv_1 : i.succ + j = n) (ys : Vector β (n - i.succ)),
      j < n →
        ∀ (this : i + (j + 1) = n),
          (∀ (__do_lift : β), motive i (j + 1) this (Vector.cast ⋯ (ys.push __do_lift))) → motive i.succ j inv_1 ys)
  (i j : Nat) (inv : i + j = n) (ys : Vector β (n - i)) : motive i j inv ys
-/
#guard_msgs in
#check mapFinIdxM'.map.induct

#guard_msgs (drop info) in
#check mapFinIdxM'.map.induct_unfolding
