/-!
Goals that need the linear facts cutsat derives for `a / k` and `a % k`. `lia` asserts them directly
into cutsat, while `grind` adds them to the E-graph. The kernel checks the proofs on both paths. The
facts inherit the generation of `a`.
-/

example (x : Int) : x % 3 < 3 := by lia
example (x : Int) : 0 ≤ x % 5 := by lia
example (x : Int) : x % (-3) < 3 := by lia
example (x : Int) (h : x % 4 = 5) : False := by lia
example (x y : Int) (h : x / 2 = y) : 2 * y ≤ x := by lia
example (x : Int) : x = 7 * (x / 7) + x % 7 := by lia
example (x : Nat) : x % 3 < 3 := by lia

example (x : Int) : x % 3 < 3 := by grind
example (x y : Int) (h : x / 2 = y) : 2 * y ≤ x := by grind
example (x : Int) : x = 7 * (x / 7) + x % 7 := by grind

/-! In `lia`, only the negated goal enters the E-graph. -/

/-- trace: [grind.assert] -1 * (x % 3) + 3 ≤ 0 -/
#guard_msgs (trace) in
set_option trace.grind.assert true in
example (x : Int) : x % 3 < 3 := by lia

/-! `grind` adds the facts to the E-graph, even when cutsat is its only arithmetic solver. -/

/--
trace: [grind.assert] -1 * (x % 3) + 3 ≤ 0
[grind.assert] x % 3 + -2 ≤ 0
[grind.assert] -1 * (x % 3) ≤ 0
[grind.assert] -1 * x + 3 * (x / 3) + x % 3 = 0
-/
#guard_msgs (trace) in
set_option trace.grind.assert true in
example (x : Int) : x % 3 < 3 := by grind -ring -linarith -ac -order

/-! The facts inherit the generation of `a`. Here `a` is `y + 1`, created by an instance of `g_eq`. -/

def g (x : Int) : Int := (x + 1) % 3
@[grind =] theorem g_eq (x : Int) : g x = (x + 1) % 3 := rfl

/--
trace: [grind.internalize] [0] y
[grind.internalize] [0] -1 * g y + 3 ≤ 0
[grind.internalize] [0] Int
[grind.internalize] [0] Int.instLEInt
[grind.internalize] [0] -1 * g y + 3
[grind.internalize] [0] instHAdd
[grind.internalize] [0] Int.instAdd
[grind.internalize] [0] -1 * g y
[grind.internalize] [0] instHMul
[grind.internalize] [0] Int.instMul
[grind.internalize] [0] -1
[grind.internalize] [0] g y
[grind.internalize] [0] 3
[grind.internalize] [0] 0
[grind.internalize] [1] (y + 1) % 3
[grind.internalize] [1] instHMod
[grind.internalize] [1] Int.instMod
[grind.internalize] [1] y + 1
[grind.internalize] [1] 1
[grind.internalize] [1] (y + 1) % 3 + -2 ≤ 0
[grind.internalize] [1] (y + 1) % 3 + -2
[grind.internalize] [1] -2
-/
#guard_msgs (trace) in
set_option trace.grind.internalize true in
example (y : Int) : g y < 3 := by grind
