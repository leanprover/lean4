/-!
Tests for dynamic variable reordering in `cutsat`. Variables created by E-matching rounds after
the first model search are appended to the variable order; when such a variable has a large
coefficient (here quotients by `2^16`), the Cooper split that eliminates it enumerates the
coefficient unless the variables are reordered again. The `grind.lia.reorder` trace pins the number
of reorderings: epoch 1 is the initial reordering, later epochs are the dynamic ones (repeated per
case-split branch).
-/

set_option linter.unusedVariables false

-- `x.toNat / 2^16` is introduced by the E-matching instance of `BitVec.toInt_eq_toNat_bmod`.
/--
trace: [grind.lia.reorder] reordering variables, epoch: 1
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 2
-/
#guard_msgs in
set_option trace.grind.lia.reorder true in
example (x : BitVec 16) : (x <<< 1).toInt = (x.toInt <<< 1).bmod (2 ^ 16) := by grind

example (x : BitVec 16) : (x <<< 1).toInt = (2 * x.toInt).bmod (2 ^ 16) := by grind
example (x : BitVec 64) : (x <<< 3).toInt = (8 * x.toInt).bmod (2 ^ 64) := by grind
example (x : BitVec 8) (h : x.toInt < 0) : (x + 1).toInt = x.toInt + 1 := by grind

-- One late E-matching round: both `g x` and `u x` are unfolded after the first search.
/--
trace: [grind.lia.reorder] reordering variables, epoch: 1
[grind.lia.reorder] reordering variables, epoch: 2
-/
#guard_msgs in
set_option trace.grind.lia.reorder true in
example (g u : Int → Int) (hg : ∀ y, g y = Int.bmod y 65536) (hu : ∀ y, u y = Int.bmod (2 * y) 65536)
    (x : Int) (hx : 0 ≤ x) (hx' : x < 65536) : u x = Int.bmod (2 * g x) 65536 := by grind

-- Chained unfoldings: each E-matching round introduces a new quotient, so a single branch goes
-- through epochs 1 to 4. With reordering restricted to once, these goals exhaust `liaSteps`.
/--
trace: [grind.lia.reorder] reordering variables, epoch: 1
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
-/
#guard_msgs in
set_option trace.grind.lia.reorder true in
example (g h : Int → Int) (hg : ∀ y, g y = Int.bmod y 65536) (hh : ∀ y, h y = Int.bmod (2 * g y) 65536)
    (x : Int) (hx : 0 ≤ x) (hx' : x < 65536) : h x = Int.bmod (2 * x) 65536 := by grind

/--
trace: [grind.lia.reorder] reordering variables, epoch: 1
[grind.lia.reorder] reordering variables, epoch: 2
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 4
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
[grind.lia.reorder] reordering variables, epoch: 3
-/
#guard_msgs in
set_option trace.grind.lia.reorder true in
example (g h k : Int → Int) (hg : ∀ y, g y = Int.bmod y 65536) (hh : ∀ y, h y = Int.bmod (2 * g y) 65536)
    (hk : ∀ y, k y = Int.bmod (2 * h y) 65536)
    (x : Int) (hx : 0 ≤ x) (hx' : x < 65536) : k x = Int.bmod (4 * x) 65536 := by grind
