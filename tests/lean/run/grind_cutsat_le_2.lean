set_option grind.warning false
set_option grind.debug true
open Int.Linear

example (a b c d e : Int) :
    2*a + b ≥ 1 → b ≥ 0 → c ≥ 0 → d ≥ 0 → e ≥ 0
    → a ≥ 3*c → c ≥ 6*e → d - e*5 ≥ 0
    → a + b + 3*c + d + 2*e ≥ 0 := by
  grind

set_option trace.grind.cutsat.model true

/--
info: [grind.cutsat.model] a := 7
[grind.cutsat.model] b := 0
[grind.cutsat.model] c := 3
[grind.cutsat.model] d := 2
-/
#guard_msgs (info) in
example (a b c d e : Int) :
    a + b ≥ 0 →
    a = 2*c + 1 →
    c*2 = 3*d →
    c + d ≤ 0 := by
  (fail_if_success grind); sorry

/--
info: [grind.cutsat.model] a := 17
[grind.cutsat.model] b := -9
[grind.cutsat.model] c := -9
-/
#guard_msgs (info) in
example (a b c : Int) :
    2*a + 3*b = 7 →
    4*a + 7*c = 5 →
    a ≥ 10 →
    False := by
  (fail_if_success grind); sorry
