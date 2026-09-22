/-!
Evaluating `Nat.shiftLeft` on literals whose shift amount does not fit in 32 bits used to abort the
process ("Nat.shiftl exponent is too big") in `whnf`, `simp`, `cbv`, `grind` and the compiler.
Such shifts are now left unevaluated.
https://github.com/leanprover/lean4/issues/15193
-/

-- `whnf` (`Meta.reduceNat?`)
/--
error: Tactic `rfl` failed: The left-hand side
  1 <<< 4294967296
is not definitionally equal to the right-hand side
  0

⊢ 1 <<< 4294967296 = 0
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by rfl

/--
error: Tactic `decide` proved that the proposition
  1 <<< 4294967296 = 0
is false
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by decide

/--
error: Tactic `rfl` failed: The left-hand side
  1 <<< 4294967296
is not definitionally equal to the right-hand side
  0

⊢ 1 <<< 4294967296 = 0
-/
#guard_msgs in
example : ((1 : Int) <<< (4294967296 : Nat)) = 0 := by rfl

-- `simp` simprocs
/--
error: `simp` made no progress
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by simp only [Nat.reduceShiftLeft]

/--
error: `simp` made no progress
-/
#guard_msgs in
example : ((1 : Fin (2^40)) <<< (4294967296 : Fin (2^40))) = 0 := by simp only [Fin.reduceShiftLeft]

/--
error: `simp` made no progress
-/
#guard_msgs in
example : ((1#8) <<< (4294967296 : Nat)) = 0#8 := by simp only [BitVec.reduceHShiftLeft]

/--
error: `simp` made no progress
-/
#guard_msgs in
example : BitVec.shiftLeftZeroExtend (1#8) 4294967296 = 0 := by
  simp only [BitVec.reduceShiftLeftZeroExtend]

-- `cbv` (`Sym` ground evaluation)
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : (1 <<< 4294967296 : Nat) = 0 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((1 : Int) <<< (4294967296 : Nat)) = 0 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((1#8) <<< (4294967296 : Nat)) = 0#8 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((1#64) <<< (4294967296#64)) = 0#64 := by cbv

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : ((1 : Fin (2^40)) <<< (4294967296 : Fin (2^40))) = 0 := by cbv

-- `grind` propagators
/--
error: `grind` failed
case grind
x : Nat
h : x = 4294967296
h_1 : ¬1 <<< x = 0
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] x = 4294967296
    [prop] ¬1 <<< x = 0
    [prop] 1 ≤ 2 ^ x
    [prop] 1 ≤ x → 2 ∣ 2 ^ x
  [eqc] True propositions
    [prop] 2 ∣ 2 ^ x
    [prop] 1 ≤ x
    [prop] 1 ≤ 2 ^ x
    [prop] 1 ≤ x → 2 ∣ 2 ^ x
  [eqc] False propositions
    [prop] 1 <<< x = 0
  [eqc] Equivalence classes
    [eqc] {x, 4294967296}
    [eqc] {2 ^ x, 1 <<< x}
    [eqc] others
      [eqc] {↑x, ↑4294967296}
      [eqc] {↑0, 0}
  [ematch] E-matching patterns
    [thm] Int.shiftLeft_zero: [@HShiftLeft.hShiftLeft `[Int] `[Nat] `[Int] `[Int.instHShiftLeftNat] #0 `[0]]
    [thm] Int.zero_shiftLeft: [@HShiftLeft.hShiftLeft `[Int] `[Nat] `[Int] `[Int.instHShiftLeftNat] `[0] #0]
    [thm] Nat.zero_shiftLeft: [@HShiftLeft.hShiftLeft `[Nat] `[Nat] `[Nat] `[instHShiftLeftOfShiftLeft] `[0] #0]
    [thm] Nat.shiftLeft_zero: [@HShiftLeft.hShiftLeft `[Nat] `[Nat] `[Nat] `[instHShiftLeftOfShiftLeft] #0 `[0]]
    [thm] Nat.pow_pos: [@HPow.hPow `[Nat] `[Nat] `[Nat] `[instHPow] #2 #1]
    [thm] Nat.div_pow_of_pos: [@HPow.hPow `[Nat] `[Nat] `[Nat] `[instHPow] #2 #1]
    [thm] Nat.dvd_mul_right_of_dvd: [@Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2,
         @HMul.hMul `[Nat] `[Nat] `[Nat] `[instHMul] #2 #0]
    [thm] Nat.dvd_mul_left_of_dvd: [@Dvd.dvd `[Nat] `[Nat.instDvd] #3 #2,
         @HMul.hMul `[Nat] `[Nat] `[Nat] `[instHMul] #0 #2]
  [cutsat] Assignment satisfying linear constraints
    [assign] x := 4294967296
    [assign] 「2 ^ x」 := 2
    [assign] 「2 ^ x」 := 2
    [assign] 1 <<< x := 2
  [ring] Ring `Int`
    [basis] Basis
      [_] ↑x + -4294967296 = 0
[grind] Issues
  [issue] ring term with unexpected instance
        2 ^ x
  [issue] exponent 4294967296 exceeds threshold for exponentiation `(exp := 1048576)`
  [issue] ring term with unexpected instance
        2 ^ x
  [issue] ring term with unexpected instance
        2 ^ x
  [issue] ring term with unexpected instance
        2 ^ x
  [issue] ring term with unexpected instance
        2 ^ x
[grind] Diagnostics
  [ematch] E-matching Diagnostics
    [thm] Theorem Instance Count
      [thm] Nat.div_pow_of_pos ↦ 1
      [thm] Nat.pow_pos ↦ 1
-/
#guard_msgs in
example (x : Nat) (h : x = 4294967296) : (1 <<< x : Nat) = 0 := by grind

/--

-/
#guard_msgs in
example (x : Nat) (h : x = 4294967296) : ((1#8) <<< x) = 0#8 := by grind

-- compiler constant folding
def shiftTooFar : Nat := 1 <<< 4294967296

-- Shifts that the runtime can evaluate are still evaluated.
example : (1 <<< 100 : Nat) = 2 ^ 100 := by rfl
example : (1 <<< 100 : Nat) = 1267650600228229401496703205376 := by simp
example : (1 <<< 100 : Nat) = 1267650600228229401496703205376 := by cbv
example : (0 <<< 4294967296 : Nat) = 0 := by simp
example : (0 <<< 4294967296 : Nat) = 0 := by decide
