import Std

set_option mvcgen.warning false
set_option warn.sorry false

open Std.Do Std Std.Iterators Std.Iterators.Types

def f {m : Type → Type} : m Unit := sorry

@[spec]
theorem Spec.forIn_iterM
    (pre : Assertion _)
    (post : PostCond Unit _)
    (step : ∀ (it : IterM (α := ArrayIterator Nat) (StateT Nat Id) Nat) (c : Unit),
      Triple (do match ← it.step with | _ => return) sorry sorry) :
    Triple (f (m := StateT Nat Id)) pre post :=
  sorry

@[spec]
theorem array_step_spec [Monad m] [WPMonad m ps]
    {it : IterM (α := ArrayIterator α) m α} {Q : PostCond (Shrink it.Step) ps} :
    Triple it.step (Q.1 sorry) spred(Q) :=
  sorry

-- This exercises the `info.simpDiscrs?` code path in `mvcgen`, from which it should return early
-- after applying the rewrite with `mkEqMPR`. Failing to return was a bug introduced in #9834.
theorem iterforin (xs : Array Nat) {P} :
    Triple (m := StateT Nat Id) (do
      let mut sum := 0
      let _ ← f
      return sum) ⌜P⌝ (⇓r => ⌜r = sorry⌝) := by
  mvcgen
  sorry
