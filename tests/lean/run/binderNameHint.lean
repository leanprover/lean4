theorem all_eq_not_any_not (l : List α) (p : α → Bool) :
    l.all p = !l.any fun x => binderNameHint x p (!p x)
  := List.all_eq_not_any_not l p

/--
error: tactic 'fail' failed
names : List String
⊢ (!names.any fun name => !"Waldo".isPrefixOf name) = true
-/
#guard_msgs in
example (names : List String) : names.all (fun name => "Waldo".isPrefixOf name) = true := by
  rw [all_eq_not_any_not]
  fail


/--
error: tactic 'fail' failed
names : List String
⊢ (names.any fun name => !"Waldo".isPrefixOf name) = false
-/
#guard_msgs in
example (names : List String) : names.all (fun name => "Waldo".isPrefixOf name) = true := by
  simp [all_eq_not_any_not, -List.any_eq_false]
  fail


def List.myAll (p : α → Bool) (xs : List α) : Bool := !(xs.any fun x => !p x)

theorem myAll_eq_not_any_not (l : List α) (p : α → Bool) :
    l.myAll p = !l.any fun x => binderNameHint x p (!p x)
  := rfl

/--
error: tactic 'fail' failed
names : List String
⊢ (!names.any fun name => !"Waldo".isPrefixOf name) = true
-/
#guard_msgs in
example (names : List String) : names.myAll (fun name => "Waldo".isPrefixOf name) = true := by
  dsimp [myAll_eq_not_any_not]
  fail
