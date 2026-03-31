import Lean

open Std.Do

set_option mvcgen.warning false

theorem set_spec : ⦃⌜True⌝⦄ set (m := StateM Nat) 42 ⦃⇓_ s => ⌜s = 42⌝⦄ := by
  mvcgen

example : True := by
  have : ⦃⌜True⌝⦄ set (m := StateM Nat) (?n : Nat) ⦃⇓_ s => ⌜s = 42⌝⦄ := by
    -- apply set_spec -- this fails, so `mspec` below should fail, too
    mintro _
    fail_if_success mspec set_spec
    have : ?n = 42 := by rfl
    mspec set_spec
  trivial
