import Std.Internal.Do
import Std.Tactic.Do

/-! A tactic `have`/`let`/`suffices` wraps the goal in `noImplicitLambda` `mdata` (via
`refine_lift no_implicit_lambda% …`). `vcgen` must read the program type through that annotation. -/

set_option mvcgen.warning false

open Std.Internal.Do Lean.Order

example : ⦃fun _ => True⦄ (pure 1 : StateM Nat Nat) ⦃fun _ _ => True⦄ := by
  have _h : True := trivial
  vcgen

example : ⦃fun _ => True⦄ (pure 1 : StateM Nat Nat) ⦃fun _ _ => True⦄ := by
  let _n : Nat := 0
  vcgen
