/--
info: [grind.offset.internalize] a1 ↦ #0
[grind.offset.internalize] a2 ↦ #1
[grind.offset.internalize] a1 + 1 ≤ a2 ↦ #0 + 1 ≤ #1
[grind.offset.internalize] a3 ↦ #2
[grind.offset.internalize] a2 ≤ a3 + 2 ↦ #1 ≤ #2 + 2
[grind.offset.internalize] a4 ↦ #3
[grind.offset.internalize] a3 ≤ a4 ↦ #2 ≤ #3
-/
#guard_msgs (info) in
set_option trace.grind.offset.internalize true in
example (a1 a2 a3) :
        a1 + 1 ≤ a2 → a2 ≤ a3 + 2 → a3 ≤ a4 → False := by
  fail_if_success grind
  sorry
