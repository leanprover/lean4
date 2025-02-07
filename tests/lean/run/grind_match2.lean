def g (a : α) (as : List α) : List α :=
  match as with
  | [] => [a]
  | b::bs => a::a::b::bs

set_option trace.grind true in
set_option trace.grind.assert true in
example : ¬ (g a as).isEmpty := by
  unfold List.isEmpty
  unfold g
  grind

def h (as : List Nat) :=
  match as with
  | []      => 1
  | [_]     => 2
  | _::_::_ => 3

/--
info: [grind] closed `grind.1`
[grind] closed `grind.2`
[grind] closed `grind.3`
-/
#guard_msgs (info) in
set_option trace.grind true in
example : h as ≠ 0 := by
  grind [h.eq_def]

example : h as ≠ 0 := by
  unfold h
  fail_if_success grind (splitMatch := false)
  sorry
