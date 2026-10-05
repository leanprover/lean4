import Lean

/-!
Runs representative elaboration with `debug.synthInstance.checkCacheHits`, the differential
validation of type class resolution cache hits: every served entry is recomputed from scratch
and compared. A panic here means a served result diverged from recomputation, i.e. some
dependency of the entry was not recorded.
-/

set_option debug.synthInstance.checkCacheHits true

class R (α : Type) where
  val : Nat

instance : R Nat := ⟨1⟩
instance : R (List α) := ⟨2⟩
instance [R α] [R β] : R (α × β) := ⟨3⟩

def f (n : Nat) : Nat := R.val Nat + n

example : R.val (List Nat) = 2 := rfl
example : R.val (List Nat) = 2 := rfl
example : R.val (Nat × List Nat) = 3 := rfl
example : R.val (Nat × List Nat) = 3 := rfl

def sumIt (l : List Nat) : Nat := l.foldl (· + ·) 0

example : sumIt [1, 2, 3] = 6 := by simp [sumIt]
example : sumIt [1, 2, 3] = 6 := by simp [sumIt]

structure Wrap where
  out : Nat

instance : R Wrap := ⟨4⟩

example (w : Wrap) : R.val Wrap + w.out = 4 + w.out := rfl

-- A cached failure of the out-param check: the search itself finds `instOPNatBool`, and only
-- assigning the out-param fails.
class OP (α : Type) (β : outParam Type) where

instance : OP Nat Bool := ⟨⟩

/--
error: failed to synthesize instance of type class
  OP Nat (List Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def op1 : Unit := let _ : OP Nat (List Nat) := inferInstance; ()

/--
error: failed to synthesize instance of type class
  OP Nat (List Nat)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
def op2 : Unit := let _ : OP Nat (List Nat) := inferInstance; ()

-- The out-param check of a hit can be stuck: output parameters are not part of the key, so an entry
-- stored for an assignable output parameter is served to a query whose output parameter cannot be
-- assigned. The recomputation is stuck in the same way and must not be reported as a mismatch.
/--
info: assignable: instOPNatBool
---
info: not assignable: stuck
-/
#guard_msgs in
open Lean Meta in
run_meta do
  let q (b : Expr) := mkApp2 (mkConst ``OP) (mkConst ``Nat) b
  let show' (r : LOption Expr) : MessageData := match r with
    | .some e => m!"{e}" | .none => "none" | .undef => "stuck"
  logInfo m!"assignable: {show' (← trySynthInstance (q (← mkFreshExprMVar (mkSort .one))))}"
  let b ← mkFreshExprMVar (mkSort .one)
  withNewMCtxDepth do
    logInfo m!"not assignable: {show' (← trySynthInstance (q b))}"
