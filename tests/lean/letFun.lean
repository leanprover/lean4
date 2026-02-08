import Lean.Elab.Command

/-!
# Tests for `have x := v; b` notation
-/

/-!
Checks that types can be inferred and that default instances work with `have`.
-/
#check
  have f x := x * 2
  have x := 1
  have y := x + 1
  f (y + x)

/-!
Checks that `simp` can do zeta reduction of `have`s
-/
example (a b : Nat) (h1 : a = 0) (h2 : b = 0) : (have x := a + 1; x + x) > b := by
  simp (config := { zeta := false }) [h1]
  trace_state
  simp (config := { decide := true }) [h2]

/-!
Checks that the underlying encoding for `have` can be overapplied.
This still pretty prints with `have` notation.
-/
#check (show Nat → Nat from id) 1

/-!
Checks that zeta reduction still occurs even if the `have` is applied to an argument.
-/
example (a b : Nat) (h : a > b) : (show Nat → Nat from id) a > b := by
  simp
  trace_state
  exact h

/-!
Checks that the type of a `have` can depend on the value.
-/
#check have n := 5
  (⟨[], Nat.zero_le n⟩ : { as : List Bool // as.length ≤ n })

/-!
Check that `have` is reducible.
-/
#check (rfl : (have n := 5; n) = 5)

/-!
Exercise `isDefEqQuick` for `have`.
-/
#check (rfl : (have _n := 5; 2) = 2)

/-!
Check that `have` responds to WHNF's `zeta` option.
-/

open Lean Meta Elab Term in
elab "#whnfCore " z?:(&"noZeta")? t:term : command => Command.runTermElabM fun _ => do
  let e ← withSynthesize <| Term.elabTerm t none
  let e ← withConfig (fun c => { c with zeta := z?.isNone }) <| Meta.whnfCore e
  logInfo m!"{e}"

#whnfCore have n := 5; n
#whnfCore noZeta have n := 5; n
