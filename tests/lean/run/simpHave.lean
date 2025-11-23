/-!
# Tests for `simp` of `have` expressions (and some `let` expressions)

Note: There are additional stress tests of deep `have`s in tests/lean/run/simpLetFunIssue.lean
-/

set_option linter.unusedSimpArgs false

-- Enable simp consistency checks, so that the elaborator type checker is run on generated proofs.
-- We want this so that we can verify that haves are "elaborator type correct",
-- since the kernel does not check `nonDep`.
set_option debug.simp.check.have true
-- To see the types of `have` binders for verification.
set_option pp.letVarTypes true

/-! Zeta reduction of lets -/
/--
trace: n : Nat
h : n = 5
⊢ 1 + 4 = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4; x + w = n := by
  simp +zeta only
  trace_state
  simp [h]

/-! Turning off zeta reduction of lets -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4; x + w = n := by
  simp -zeta -zetaUnused -letToHave only

/-! Turning off zeta reduction of lets. Lets can only be dsimped. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4; x + w = n := by
  simp -zeta -zetaUnused -letToHave only [h]
/--
trace: n : Nat
h : n = 5
⊢ let x : Nat := 1;
  let _y : Nat := 2;
  let _z : Nat := 3;
  let w : Nat := 4;
  x + w = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4 + 0; x + w = n + 0 := by
  simp -zeta -zetaUnused -letToHave only [h, Nat.add_zero]
  trace_state
  simp [h]

/-! letToHave -/
/--
error: unsolved goals
n : Nat
h : n = 5
⊢ have x : Nat := 1;
  have _y : Nat := 2;
  have _z : Nat := 3;
  have w : Nat := 4;
  x + w = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4; x + w = n := by
  simp -zeta -zetaUnused +letToHave only

/-! Enabling zetaUnused for lets -/
/--
trace: n : Nat
h : n = 5
⊢ let x : Nat := 1;
  let w : Nat := 4;
  x + w = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; let _y := 2; let _z := 3; let w := 4; x + w = n := by
  simp -zeta +zetaUnused -letToHave only
  trace_state
  simp [h]

/-! Zeta reduction of haves -/
/--
trace: n : Nat
h : n = 5
⊢ 1 + 4 = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    have x := 1; have _y := 2; have _z := 3; have w := 4; x + w = n := by
  simp +zeta only
  trace_state
  simp [h]

/-! Turning off zeta reduction of haves, including with specific `zetaHave` option. -/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    have x := 1; have _y := 2; have _z := 3; have w := 4; x + w = n := by
  simp -zeta -zetaUnused only
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    have x := 1; have _y := 2; have _z := 3; have w := 4; x + w = n := by
  simp -zetaHave -zetaUnused only

/-! Enabling zetaUnused for haves, and just haves -/
/--
trace: n : Nat
h : n = 5
⊢ have x : Nat := 1;
  have w : Nat := 4;
  x + w = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    have x := 1; have _y := 2; have _z := 3; have w := 4; x + w = n := by
  simp -zeta +zetaUnused only
  trace_state
  simp [h]
/--
trace: n : Nat
h : n = 5
⊢ have x : Nat := 1;
  have w : Nat := 4;
  x + w = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    have x := 1; have _y := 2; have _z := 3; have w := 4; x + w = n := by
  simp -zetaHave +zetaUnused only
  trace_state
  simp [h]

/-! Zeta reduction, but no zeta reduction of haves. -/
/--
trace: n : Nat
h : n = 5
⊢ have y : Nat := 2 + 1;
  have _z : Nat := 3 + 1 + y;
  1 + 4 = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; have y := 2 + x; have _z := 3 + x + y; let w := 4; x + w = n := by
  simp +zeta -zetaHave -zetaUnused -letToHave only
  trace_state
  simp [h]
/--
trace: n : Nat
h : n = 5
⊢ have y : Nat := 3;
  have _z : Nat := 4 + y;
  5 = n
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    let x := 1; have y := 2 + x; have _z := 3 + x + y; let w := 4; x + w = n := by
  simp +zeta -zetaHave -zetaUnused -letToHave [Nat.reduceAdd]
  trace_state
  simp [h]

def fix1 (n : Nat) : Fin (n + 1) := 0

/-!
Fixed because appears in type of body.
-/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    (have a := n + 1; fix1 a) = 0 := by
  simp -zeta -zetaUnused [h]

/-!
Fixed, but can dsimp value.
-/
/--
trace: n : Nat
_h : n = 5
⊢ (have a : Nat := n + 1;
    fix1 a) =
    0
-/
#guard_msgs in
example (n : Nat) (_h : n = 5) :
    (have a := n + 0 + 1; fix1 a) = 0 := by
  simp -zeta -zetaUnused [_h]
  trace_state
  simp [fix1]

/-!
Check that zetaUnused doesn't affect this.
-/
/--
trace: n : Nat
_h : n = 5
⊢ (have a : Nat := n + 1;
    fix1 a) =
    0
-/
#guard_msgs in
example (n : Nat) (_h : n = 5) :
    (have _u0 := 0; have a := n + 0 + 1; have _u1 := 1; fix1 a) = 0 := by
  simp -zeta +zetaUnused [_h]
  trace_state
  simp [fix1]

/-!
Appears in the type of another `have` in telescope, but not fixed.
-/
/--
trace: n : Nat
h : n = 5
⊢ (have a : Nat := 6;
    have b : Fin (a + 1) := fix1 a;
    ↑b) =
    0
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    (have a := 0 + n + 1; have b := 0 + fix1 a + 0; (b : Nat)) = 0 := by
  simp -zeta -zetaUnused [h]
  trace_state
  simp [fix1]

/-!
Check that zetaUnused doesn't affect this.
-/
/--
trace: n : Nat
h : n = 5
⊢ (have a : Nat := 6;
    have b : Fin (a + 1) := fix1 a;
    ↑b) =
    0
-/
#guard_msgs in
example (n : Nat) (h : n = 5) :
    (have _u0 := 0; have a := 0 + n + 1; have _u1 := 1; have b := 0 + fix1 a + 0; have _u2 := 2; (b : Nat)) = 0 := by
  simp -zeta +zetaUnused [h]
  trace_state
  simp [fix1]

/-!
Transitively unused `have`s.
-/
/--
trace: ⊢ have m : Nat := 1;
  have n : Nat := 1;
  n = m
-/
#guard_msgs in
example :
    have m := 1; have u0 := 0; have u1 := u0; have n := 1; have u2 := u1; have u3 := u2; have _u4 := u3; n = m := by
  simp -zeta
  trace_state
  simp

/-!
Unused, unfixed, fixed, all six permutations, with a changing body.
-/
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have _u1 := 1; have a := 0 + n; have b := 0 + n; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have a := 0 + n; have _u1 := 1; have b := 0 + n; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have a := 0 + n; have b := 0 + n; have _u1 := 1; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have _u1 := 1; have b := 0 + n; have a := 0 + n; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have b := 0 + n; have _u1 := 1; have a := 0 + n; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have b := 0 + n; have a := 0 + n; have _u1 := 1; (0 + a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl

/-!
Unused, unfixed, fixed, all six permutations, with an unchanging body.
-/
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have _u1 := 1; have a := 0 + n; have b := 0 + n; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have a := 0 + n; have _u1 := 1; have b := 0 + n; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have a : Nat := n;
    have b : Nat := 0 + n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have a := 0 + n; have b := 0 + n; have _u1 := 1; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have _u1 := 1; have b := 0 + n; have a := 0 + n; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have b := 0 + n; have _u1 := 1; have a := 0 + n; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl
/--
trace: n : Nat
⊢ (have b : Nat := 0 + n;
    have a : Nat := n;
    (a, fix1 b)) =
    (n, 0)
-/
#guard_msgs in
example (n : Nat) :
    (have b := 0 + n; have a := 0 + n; have _u1 := 1; (a, fix1 b)) = (n, 0) := by
  simp -zeta
  trace_state
  rfl

/-!
Unused tests: modifying and not modifying body.
-/
/--
trace: n : Nat
h : n = 1
⊢ n = 1
-/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have _u1 := n; 0 + n) = 1 := by
  simp -zeta
  trace_state
  simp [h]
/--
trace: n : Nat
h : n = 1
⊢ n = 1
-/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have _u1 := n; n) = 1 := by
  simp -zeta
  trace_state
  simp [h]

/-!
Non-fixed tests: modifying and not modifying value and body.
-/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have m := n; m) = 1 := by
  simp -zeta -zetaUnused
/--
trace: n : Nat
h : n = 1
⊢ (have m : Nat := n;
    m) =
    1
-/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have m := n; 0 + m) = 1 := by
  simp -zeta
  trace_state
  simp [h]
/--
trace: n : Nat
h : n = 1
⊢ (have m : Nat := n;
    m) =
    1
-/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have m := 0 + n; m) = 1 := by
  simp -zeta
  trace_state
  simp [h]
/--
trace: n : Nat
h : n = 1
⊢ (have m : Nat := n;
    m) =
    1
-/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have m := 0 + n; 0 + m) = 1 := by
  simp -zeta
  trace_state
  simp [h]

/-!
Fixed tests: modifying and not modifying body (with simp) and value (with dsimp)
-/
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 1) :
    (have m := n; fix1 m) = 1 := by
  simp -zeta -zetaUnused
/--
trace: n : Nat
h : n = 0
⊢ (have m : Nat := n;
    fix1 m) =
    Fin.ofNat (n + 1) n
-/
#guard_msgs in
example (n : Nat) (h : n = 0) :
    (have m := n; 0 + fix1 m) = Fin.ofNat (n + 1) n := by
  simp -zeta
  trace_state
  simp [h, fix1]
/-- error: `simp` made no progress -/
#guard_msgs in
example (n : Nat) (h : n = 0) :
    (have m := 0 + n; fix1 m) = n := by
  simp -zeta
  trace_state
  simp [h, fix1]; rfl
/--
trace: n : Nat
h : n = 0
⊢ (have m : Nat := n;
    fix1 m) =
    Fin.ofNat (n + 1) n
-/
#guard_msgs in
example (n : Nat) (h : n = 0) :
    (have m := n + 0; fix1 m) = Fin.ofNat (n + 1) n := by
  simp -zeta
  trace_state
  simp [h, fix1]
/--
trace: n : Nat
h : n = 0
⊢ (have m : Nat := 0 + n;
    fix1 m) =
    Fin.ofNat (0 + n + 1) n
-/
#guard_msgs in
example (n : Nat) (h : n = 0) :
    (have m := 0 + n; 0 + fix1 m) = Fin.ofNat (0 + n + 1) n := by
  simp -zeta
  trace_state
  simp [h, fix1]
/--
trace: n : Nat
h : n = 0
⊢ (have m : Nat := n;
    fix1 m) =
    Fin.ofNat (n + 1) n
-/
#guard_msgs in
example (n : Nat) (h : n = 0) :
    (have m := n + 0; 0 + fix1 m) = Fin.ofNat (n + 0 + 1) n := by
  simp -zeta
  trace_state
  simp [h, fix1]

/-!
Stress test
-/
def lp (n : Nat) (acc : Nat) :=
  match n with
  | 0 => acc
  | n' + 1 => have k := 0 + acc + n'; lp n' k

/--
trace: n : Nat
h : n = 190
⊢ (have k : Nat := 0 + 0 + 19;
    have k : Nat := 0 + k + 18;
    have k : Nat := 0 + k + 17;
    have k : Nat := 0 + k + 16;
    have k : Nat := 0 + k + 15;
    have k : Nat := 0 + k + 14;
    have k : Nat := 0 + k + 13;
    have k : Nat := 0 + k + 12;
    have k : Nat := 0 + k + 11;
    have k : Nat := 0 + k + 10;
    have k : Nat := 0 + k + 9;
    have k : Nat := 0 + k + 8;
    have k : Nat := 0 + k + 7;
    have k : Nat := 0 + k + 6;
    have k : Nat := 0 + k + 5;
    have k : Nat := 0 + k + 4;
    have k : Nat := 0 + k + 3;
    have k : Nat := 0 + k + 2;
    have k : Nat := 0 + k + 1;
    have k : Nat := 0 + k + 0;
    k) =
    n
-/
#guard_msgs in
example (n : Nat) (h : n = 190) : lp 20 0 = n := by
  simp -zeta only [lp]
  trace_state
  simp -zeta only [Nat.zero_add]
  simp only
  simp [h]

-- set_option Elab.async false
-- set_option profiler true
-- set_option profiler.threshold 2
-- #time
set_option debug.simp.check.have false in
example (n : Nat) (h : n = 4950) : lp 100 0 = n := by
  simp -zeta -zetaUnused only [lp]
  simp -zeta only [Nat.zero_add]
  simp only
  simp [h]
