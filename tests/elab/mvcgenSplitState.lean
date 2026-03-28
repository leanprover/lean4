import Std.Tactic.Do

open Std.Do

/-!
Tests that `mvcgen` is able to split the goal
```
⊢ₛ
wp⟦match s with
    | none => pure 0
    | some x => pure x⟧
  (PostCond.noThrow fun x => ⌜True⌝) s
```
Note that `s` is an excess state variable that does not only occur in the program, but also in the
application of the predicate transformer.
-/

set_option mvcgen.warning false in
example :
  ⦃⌜True⌝⦄
  (do
    let s ← get (m := StateM (Option Nat))
    match s with
    | none => pure 0
    | some x => pure x)
  ⦃⇓_ => ⌜True⌝⦄ := by
  mvcgen
