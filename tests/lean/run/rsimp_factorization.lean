import Std.Tactic.RSimp

-- An example rsimpset

-- Unfortunately, `attribute` does not allow to add theorems with symm := true

@[rsimp] def Nat.beq_eq_symm {x y : Nat} : (x = y) = (x.beq y = true) := (@Nat.beq_eq x y).symm
attribute [rsimp] Nat.dvd_iff_mod_eq_zero
@[rsimp] def Bool.cond_decide_symm := fun α p inst t e => (@Bool.cond_decide α p inst t e).symm
attribute [rsimp] Std.Tactic.BVDecide.Normalize.Bool.decide_eq_true
attribute [rsimp] Bool.decide_and

@[rsimp] def Nat.ble_eq_symm := fun a b => (@Nat.ble_eq a b).symm
@[rsimp] def Nat.blt_eq_symm := fun a b => (@Nat.blt_eq a b).symm
@[rsimp] def Nat.mod_eq_symm (a b : Nat) : a % b = Nat.mod a b := rfl
@[rsimp] def Nat.add_eq_symm := fun a b => (@Nat.add_eq a b).symm
@[rsimp] def Nat.mul_eq_symm := fun a b => (@Nat.mul_eq a b).symm

-- Somehow, simp does not like unfolding cond.match_1
-- attribute [rsimp] cond cond.match_1
@[rsimp] theorem cond_eq_rec (b : Bool) (t e : α) : cond b t e = b.rec e t := by
  cases b <;> rfl

@[semireducible] def minFacAux (n : Nat) : Nat → Nat
  | k =>
    if n < k * k then n
    else
      if k ∣ n then k
      else
        minFacAux n (k + 2)
termination_by k => n + 2 - k
decreasing_by sorry

def minFac (n : Nat) : Nat := if 2 ∣ n then 2 else minFacAux n 3
def isPrime (p : Nat) : Bool := 2 ≤ p ∧ minFac p = p

/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example : isPrime 524287 := by decide

attribute [rsimp_optimize] minFacAux
attribute [rsimp_optimize] minFac
attribute [rsimp_optimize] isPrime

/--
info: def minFacAux.rsimp : Nat → Nat → Nat :=
rsimp_iterate minFacAux fun ih n x => Bool.rec (Bool.rec (ih n (x.add 2)) x ((n.mod x).beq 0)) n (n.blt (x.mul x))
-/
#guard_msgs in
#print minFacAux.rsimp

/--
info: def minFac.rsimp : Nat → Nat :=
fun n => Bool.rec (minFacAux.rsimp n 3) 2 ((n.mod 2).beq 0)
-/
#guard_msgs in
#print minFac.rsimp

/--
info: def isPrime.rsimp : Nat → Bool :=
fun p => Nat.ble 2 p && (minFac.rsimp p).beq p
-/
#guard_msgs in
#print isPrime.rsimp


set_option trace.tactic.rsimp_decide true in

/--
info: [tactic.rsimp_decide] Optimized expression:
      isPrime.rsimp 524287
-/
#guard_msgs in
example : isPrime 524287 := by rsimp_decide

-- 6ms:
-- #time example : isPrime 524287 := by rsimp_decide
-- 25ms:
-- #time example : isPrime 10000019 := by rsimp_decide


-- For larger ones, we get deep kernel recursion. I wonder what's recursive here?

set_option trace.tactic.rsimp_decide.debug true in
/--
error: tactic 'rsimp_decide' failed, this may be because the proposition is false, involves non-computable axioms or opaque definitions.
⊢ isPrime 100000007 = true
---
info: [tactic.rsimp_decide.debug] mkAuxLemma failed: (kernel) deep recursion detected
-/
#guard_msgs in
example : isPrime 100000007 := by rsimp_decide
