import Lean.Elab.Command

/-!
# Tests for `let_fun x := v; b` notation
-/

/-!
Checks that types can be inferred and that default instances work with `let_fun`.
-/
#check
  let_fun f x := x * 2
  let_fun x := 1
  let_fun y := x + 1
  f (y + x)

/-!
Checks that `simp` can do zeta reduction of `let_fun`s
-/
example (a b : Nat) (h1 : a = 0) (h2 : b = 0) : (let_fun x := a + 1; x + x) > b := by
  simp (config := { zeta := false }) [h1]
  trace_state
  simp (config := { decide := true }) [h2]

/-!
Checks that the underlying encoding for `let_fun` can be overapplied.
This still pretty prints with `let_fun` notation.
-/
#check (show Nat → Nat from id) 1

/-!
Checks that zeta reduction still occurs even if the `let_fun` is applied to an argument.
-/
example (a b : Nat) (h : a > b) : (show Nat → Nat from id) a > b := by
  simp
  trace_state
  exact h

/-!
Checks that the type of a `let_fun` can depend on the value.
-/
#check let_fun n := 5
  (⟨[], Nat.zero_le n⟩ : { as : List Bool // as.length ≤ n })

/-!
Check that `let_fun` is reducible.
-/
#check (rfl : (let_fun n := 5; n) = 5)

/-!
Exercise `isDefEqQuick` for `let_fun`.
-/
#check (rfl : (let_fun _n := 5; 2) = 2)

/-!
Check that `let_fun` responds to WHNF's `zeta` option.
-/

open Lean Elab Term in
elab "#whnfCore " z?:(&"noZeta")? t:term : command => Command.runTermElabM fun _ => do
  let e ← withSynthesize <| Term.elabTerm t none
  let e ← Meta.whnfCore e {zeta := z?.isNone}
  logInfo m!"{e}"

#whnfCore let_fun n := 5; n
#whnfCore noZeta let_fun n := 5; n
