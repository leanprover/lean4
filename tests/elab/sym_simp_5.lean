import Lean
open Lean Meta Elab Tactic

elab "sym_simp" "[" declNames:ident,* "]" : tactic => do
  let rewrite ← Sym.mkSimprocFor (← declNames.getElems.mapM fun s => realizeGlobalConstNoOverload s.raw) Sym.Simp.dischargeSimpSelf
  let methods : Sym.Simp.Methods := {
    pre  := Sym.Simp.simpTelescope
    post := Sym.Simp.evalGround.andThen rewrite
  }
  liftMetaTactic1 fun mvarId => Sym.SymM.run do
    let mvarId ← Sym.preprocessMVar mvarId
    (← Sym.simpGoal mvarId methods).toOption

set_option warn.sorry false

/-!
Recall that `simpTelescope` does not simplify the body of a telescope.
This is why `0 + x = 0 + id x` is not simplified in the following example.
-/
/--
trace: p q : Prop
⊢ q →
    ∀ (x : Nat),
      p →
        have x := x;
        have y := x;
        x = y → 0 + x = 0 + id x
-/
#guard_msgs in
example (p q : Prop) : q → ∀ x : Nat, p ∧ True → have x := 0 + x; have y := x; True → x = 0 + 0 + id y → 0 + x = 0 + id x := by
  sym_simp [and_true, Nat.zero_add, id_eq]
  trace_state
  admit
