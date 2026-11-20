import Std.Tactic.Do

/-!
Regression test for #12048: `mvcgen` on a program calling an `@[spec]` definition and a spec with a
hypothesis.
-/

set_option sym.debug true

open Std.Do

axiom myfun : Except String Unit

@[spec]
axiom myfun_spec (h : True) :
  ⦃ ⌜ True ⌝ ⦄
  myfun
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄

@[spec]
def anotherfun : Except String Unit :=
  if true then pure () else pure ()

noncomputable def program : Except String Unit := do
  anotherfun
  myfun

@[spec]
theorem spec :
  ⦃ ⌜ True ⌝ ⦄
  program
  ⦃ ⇓ _ => ⌜ True ⌝ ⦄ := by
  mvcgen [program]
