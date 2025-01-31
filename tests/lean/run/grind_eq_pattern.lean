%reset_grind_attrs

/--
info: [grind.ematch.pattern] List.append_ne_nil_of_left_ne_nil: [@HAppend.hAppend ? ? ? ? #2 #0]
-/
#guard_msgs (info) in
set_option trace.grind.ematch.pattern true in
attribute [grind] List.append_ne_nil_of_left_ne_nil

/--
info: [grind.ematch.pattern] List.append_ne_nil_of_right_ne_nil: [@HAppend.hAppend ? ? ? ? #1 #2]
-/
#guard_msgs (info) in
set_option trace.grind.ematch.pattern true in
attribute [grind] List.append_ne_nil_of_right_ne_nil
/--
info: [grind.ematch.pattern] List.getLast?_eq_some_iff: [@List.getLast? #2 #1, @some ? #0]
-/
#guard_msgs (info) in
set_option trace.grind.ematch.pattern true in
attribute [grind =] List.getLast?_eq_some_iff

/--
info: [grind.assert] xs.getLast? = b?
[grind.assert] b? = some 10
[grind.assert] xs = []
[grind.assert] (xs.getLast? = some 10) = ∃ ys, xs = ys ++ [10]
[grind.assert] xs = w ++ [10]
[grind.assert] ¬w ++ [10] = []
-/
#guard_msgs (info) in
set_option trace.grind.assert true in
example (xs : List Nat) : xs.getLast? = b? → b? = some 10 → xs ≠ [] := by
  grind
