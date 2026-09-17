/-
Demo: the `WP.wpTrans → WP.trans` rename is backward compatible.

The `WP` class carries both names as fields with mutual default values:

  class WP … where
    trans             : Prog → PredTrans …            := wpTrans
    wpTrans           : Prog → PredTrans …            := trans              -- deprecated
    trans_monotone    (x) : (trans x).Monotone        := wp_trans_monotone x
    wp_trans_monotone (x) : (trans x).Monotone        := trans_monotone x   -- deprecated
  attribute [deprecated WP.trans (since := …)]           WP.wpTrans
  attribute [deprecated WP.trans_monotone (since := …)]  WP.wp_trans_monotone

So an instance may define EITHER name; the other is filled from the default.

Where the deprecation warning fires:
  - Providing a field in a `where` block  → NO warning (it is a field label,
    not a reference to the deprecated projection constant).
  - Referencing the old projection name    → warning (it is a constant reference,
    which is what `@[deprecated]` watches).

Run with:  lean WPDeprecationDemo.lean
-/
import Std.WP
open Std.WP Lean.Order

inductive P0 | mk
inductive P1 | mk

/-- (1) NEW-style instance: define `trans` + `trans_monotone`.
    → compiles, NO warning. -/
instance iNew : WP P0 Unit Prop (Unit → Prop) where
  trans _ := ⟨fun Q _ => Q ()⟩
  trans_monotone _ := by intro _ _ _ _ _ h; exact h ()

/-- (2) OLD-style instance: define `wpTrans` + `wp_trans_monotone`.
    → compiles, NO warning (this construction hard-errored under a plain rename). -/
instance iOld : WP P1 Unit Prop (Unit → Prop) where
  wpTrans _ := ⟨fun Q _ => Q ()⟩
  wp_trans_monotone _ := by intro _ _ _ _ _ h; exact h ()

/-- (3) Read via the NEW projection name → NO warning. -/
example : PredTrans Prop (Unit → Prop) Unit := WP.trans (self := iNew) P0.mk

/-- (4) Read via the OLD projection name → DEPRECATION WARNING here:
    "`Std.WP.WP.wpTrans` has been deprecated: Use `Std.WP.WP.trans` instead". -/
example : PredTrans Prop (Unit → Prop) Unit := WP.wpTrans (self := iOld) P1.mk
