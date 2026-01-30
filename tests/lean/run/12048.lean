import Std.Tactic.Do
open Std.Do

set_option mvcgen.warning false

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
