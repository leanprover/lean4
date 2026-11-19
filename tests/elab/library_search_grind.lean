/-!
# Tests for `exact? +grind` and `apply? +grind`

These tests verify that the `+grind` option is accepted syntactically and
enables `grind` as a fallback discharger for subgoals.
-/

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos h
-/
#guard_msgs in
example (l : List Nat) (h : 0 < l.length) : l ≠ [] := by exact?

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (h trivial)
-/
#guard_msgs in
example (l : List Nat) (h : True → 0 < l.length) : l ≠ [] := by exact?

example (l : List Nat) (h : 1 < l.length) : l ≠ [] := by exact List.ne_nil_of_length_pos (by grind)

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (by grind)
-/
#guard_msgs in
example (l : List Nat) (h : 1 < l.length) : l ≠ [] := by
  exact? +grind

/--
info: Try this:
  [apply] exact List.ne_nil_of_length_pos (by grind)
-/
#guard_msgs in
example {P : Prop} (l : List Nat) (p : P) (h : P → 1 < l.length) : l ≠ [] := by
  exact? +grind

axiom foo (x : Nat) : x < 37 → 5 < x → x.log2 < 6

/--
info: Try this:
  [apply] exact foo x (by grind) (by grind)
-/
#guard_msgs in
example (x : Nat) (h₁ : x < 30) (h₂ : 8 < x) : x.log2 < 6 := by
  exact? +grind


inductive MyList (α : Type _) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

axiom MyListProp : MyList α → Prop
axiom MyListProp2 : MyList α → Prop

@[grind .] axiom mylist_nil : MyListProp (MyList.nil : MyList α)
@[grind .] axiom mylist_cons : ∀ (x : α) (xs : MyList α), MyListProp xs → MyListProp (MyList.cons x xs)

/--
info: Try these:
  [apply] (induction xs) <;> grind
  [apply] (induction xs) <;> grind only [mylist_nil, mylist_cons]
  [apply] ·
    induction xs
    · grind => instantiate only [mylist_nil]
    · grind => instantiate only [mylist_cons]
-/
#guard_msgs in
example (xs : MyList α) : MyListProp xs := by
  try?

axiom qux (xs : MyList α) (p : MyListProp xs) : MyListProp2 xs

/--
info: Try these:
  [apply] (induction xs) <;> grind
  [apply] (induction xs) <;> grind only [mylist_nil, mylist_cons]
  [apply] ·
    induction xs
    · grind => instantiate only [mylist_nil]
    · grind => instantiate only [mylist_cons]
-/
#guard_msgs in
example (xs : MyList α) : MyListProp2 xs := by
  exact qux xs (by try?)

/--
info: Try this:
  [apply] exact qux xs (by try?)
-/
example (xs : MyList α) : MyListProp2 xs := by
  exact? +try?
