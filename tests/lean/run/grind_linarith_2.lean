open Lean Grind

example [IntModule α] [Preorder α] [IntModule.IsOrdered α] (a b : α)
    : a + b = b + a  := by
  grind

/--
trace: [grind.debug.proof] Classical.byContradiction fun h =>
      let ctx := RArray.leaf One.one;
      let rctx := RArray.branch 1 (RArray.leaf a) (RArray.leaf b);
      let re_1 := (CommRing.Expr.var 1).add (CommRing.Expr.var 0);
      let re_2 := (CommRing.Expr.var 0).add (CommRing.Expr.var 1);
      let rp_1 := CommRing.Poly.num 0;
      let e_1 := Expr.zero;
      let e_2 := Expr.mul 0 (Expr.var 0);
      let p_1 := Poly.nil;
      diseq_unsat ctx
        (diseq_norm ctx e_2 e_1 p_1 (Eq.refl true) (CommRing.diseq_norm rctx re_2 re_1 rp_1 (Eq.refl true) h))
-/
#guard_msgs in
open Linarith in
set_option trace.grind.debug.proof true in
example [CommRing α] [Preorder α] [Ring.IsOrdered α] (a b : α)
    : a + b = b + a  := by
  grind -ring

-- Temporary test. TODO: delete after we implement backtracking
/--
trace: [grind.debug.linarith.search.assign] One.one := 1
[grind.debug.linarith.search.assign] b := 1
[grind.debug.linarith.search.assign] c := 2
[grind.debug.linarith.search.assign] d := 2
[grind.debug.linarith.search.assign] d := 3
[grind.debug.linarith.search.assign] a := 7/2
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.debug.linarith.search.assign true in
example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
    : b ≥ 0 → c > b → d > b → a ≠ b + c → a > b + c → a < b + d →  False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c d : α)
    : a ≤ b → a ≥ c + d → d = 0 → b = c → a = b := by
  grind

example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c d : α)
    : a ≤ b → a ≥ c + d → d ≤ 0 → d ≥ 0 → b = c → a = b := by
  grind

open Linarith RArray
set_option trace.grind.debug.proof true in
example [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (a b c d : α)
    : a ≤ b → a - c ≥ 0 + d → d ≤ 0 → d ≥ 0 → b = c → a ≠ b → False := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c : α)
    : a + 2*b = 0 → c + b = -b → a = c := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c : α)
    : a + 2*b = 0 → a = c → c + b = -b := by
  grind

example [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (a b c : α)
    : c = a → a + b ≤ 3 → 3 ≤ b + c → a + b = 3 := by
  grind
