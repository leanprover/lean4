import Std.Tactic.Do
import Std.Internal.Do

/-!
Regression test for `vcgen`'s spec backward-rule cache. The rule built from an equality spec must
stay generic in the spec's value variables: the cache reuses the rule for every program matching
the same spec theorem, so a rule specialized to the first matched program (e.g. `recf 3` below,
whose unfolding produces the recursive call `recf 2` handled by the same equation) fails on the
next one.
-/

set_option mvcgen.warning false

def recf (n : Nat) : Id Nat :=
  match n with | 0 => pure 1 | n + 1 => recf n

def myid (a : Nat) : Id Nat :=
  pure a

def myid2 (a : α) : Id α :=
  pure a

section
open Lean.Order Std.Internal.Do

-- The same equation `recf.eq_2` matches both `recf 3` and the recursive call `recf 2`.
example : ⦃ True ⦄ recf 3 ⦃ fun r => r > 0 ⦄ := by
  vcgen [recf] with finish

-- The same equation `myid.eq_1` matches two calls with different arguments.
example : ⦃ True ⦄ (do let x ← myid 3; let y ← myid 5; pure (x + y) : Id Nat) ⦃ fun r => r > 0 ⦄ := by
  vcgen [myid] with finish

-- The same equation `myid2.eq_1` matches calls at two different value types.
example :
    ⦃ True ⦄ (do let x ← myid2 3; let y ← myid2 "st"; pure (x + y.length) : Id Nat)
    ⦃ fun r => r > 0 ⦄ := by
  vcgen [myid2] with finish
end
