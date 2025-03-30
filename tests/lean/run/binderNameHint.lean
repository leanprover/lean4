theorem all_eq_not_any_not (l : List α) (p : α → Bool) :
    l.all p = !l.any fun x => binderNameHint x p (!p x)
  := List.all_eq_not_any_not

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

-- Check if we can pick the second binder by providing arguments to `f` in `binderNameHint`
-- (It will beta-reduce it)


-- Why this not in standard lib (maybe with the more complex form of recognizing lambdas that
-- ignore arguments?)
@[simp]
theorem List.mapIdx_eq_map (l : List α) (f : α → β) : (l.mapIdx fun _ x => f x) = l.map f := by
  induction l <;> simp_all

set_option linter.unusedVariables false in
theorem zipWith_eq_map_idx_zipWith (l1 : List α) (l2 : List β) (f : α → β → γ) :
    List.zipWith f l1 l2 = (List.zip l1 l2).mapIdx
      (fun i ⟨a, b⟩ => binderNameHint a f <| binderNameHint b (f a) <| f a b)
  := by simp [List.zip_eq_zipWith, List.map_zipWith]

/--
error: tactic 'fail' failed
l1 l2 : List Nat
⊢ (List.mapIdx
        (fun i x =>
          match x with
          | (x, y) => x + y)
        (l1.zip l2)).isEmpty =
    true
-/
#guard_msgs in
example (l1 l2 : List Nat) :
  (List.zipWith  (fun x y => x + y) l1 l2).isEmpty := by
  rw [zipWith_eq_map_idx_zipWith]
  fail

-- For now, binder name hints do not work in other tactics, like `apply`
-- (but at least `simp` or `dsimp` removes them)

theorem myAll_eq_not_any_not_iff {l : List α} {p : α → Bool} :
    l.myAll p ↔ !l.any fun x => binderNameHint x p (!p x)
  := by simp [myAll_eq_not_any_not]

/--
error: unsolved goals
names : List String
⊢ (!names.any fun x => !"Waldo".isPrefixOf x) = true
---
info: names : List String
⊢ (!names.any fun x => binderNameHint x (fun name => "Waldo".isPrefixOf name) !"Waldo".isPrefixOf x) = true
-/
#guard_msgs in
example (names : List String) : names.myAll (fun name => "Waldo".isPrefixOf name) = true := by
  apply myAll_eq_not_any_not_iff.mpr
  trace_state
  dsimp
  done
