import Lean
import Std.Internal
import Std.Tactic.Do

/-! Tests for `vcgen +jp`: shared-continuation (`__do_jp`) handling. A shared tail after an `if`
makes do-elaboration emit a `__do_jp`; `+jp` proves the tail once and discharges each jump through
a synthetic spec instead of inlining it. -/

open Lean Order Meta Elab Tactic Sym Std Internal.Do

set_option grind.warning false
set_option mvcgen.warning false

def ifs_pure (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  if n > 1 then x := x + 3 else x := x + 4
  return x

theorem ifs_pure_triple : ⦃ True ⦄ ifs_pure n ⦃ fun r => r > 0 ⦄ := by
  unfold ifs_pure
  vcgen +jp
  all_goals grind

def if_state (f : Nat → Bool) : StateM Nat Nat := do
  let mut x := 0
  if f 0 then x := x + 1 else x := x + 2
  return x

theorem if_state_triple : ⦃ fun _ => True ⦄ if_state f ⦃ fun r => ⌜r > 0⌝ ⦄ := by
  unfold if_state
  vcgen +jp
  all_goals grind

def ifs_pure_simple (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  return x

theorem ifs_pure_simple_triple : ⦃ True ⦄ ifs_pure_simple n ⦃ fun r => r > 0 ⦄ := by
  unfold ifs_pure_simple
  vcgen +jp
  all_goals grind
