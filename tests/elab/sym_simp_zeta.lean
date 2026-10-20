import Std.Tactic.Do

/-!
`Sym.simp` rewrite theorems must preserve nondep `let`s (e.g. do-notation `__do_jp`
join points) in their RHS. Previously `preprocessType` zeta-reduced the whole theorem
type, inlining the join points before `mvcgen +jp` could detect them. The LHS/pattern
is still zeta-reduced (matching requires `let`-free patterns).
-/

open Std.Do

set_option warn.sorry false

def step (n : Nat) : Id Nat := do
  let mut x := 0
  if n > 0 then x := x + 1 else x := x + 2
  return x

/--
trace: case grind
n : Nat
⊢ ⦃⌜True⌝⦄
    have x := 0;
    have __do_jp := fun __r => pure;
    if 0 < n then
      have x := x + 1;
      __do_jp PUnit.unit x
    else
      have x := x + 2;
      __do_jp PUnit.unit x ⦃(fun x => ⌜True⌝, ExceptConds.false)⦄
-/
#guard_msgs (trace) in
example : ⦃⌜True⌝⦄ step n ⦃⇓ _ => ⌜True⌝⦄ := by
  sym =>
    simp [step.eq_def]
    tactic => trace_state; sorry
