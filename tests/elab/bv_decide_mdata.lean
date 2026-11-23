import Lean
import Std.Tactic.BVDecide

/-!
Regression test for mdata in bv_decide's `cond` preprocessor.
-/

set_option trustCompiler true

open Lean Elab Term

syntax "mdata% " term : term

elab_rules : term
  | `(mdata% $t) => return .mdata {} (← elabTerm t none)

theorem mdata_cond (b : Bool) :
    (mdata% (bif b then true else false)) = b := by
  bv_decide
