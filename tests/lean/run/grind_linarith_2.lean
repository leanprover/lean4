module
open Std Lean Grind
set_option grind.debug true

example [IntModule α] [LE α] [LT α] [IsPreorder α] [OrderedAdd α] (a b : α)
    : a + b = b + a  := by
  grind

/--
trace: [grind.debug.proof] Classical.byContradiction fun h =>
      let ctx := RArray.leaf One.one;
      let p_1 := Poly.nil;
      let e_1 := Expr.zero;
      let e_2 := Expr.intMul 0 (Expr.var 0);
      let rctx := RArray.branch 1 (RArray.leaf a) (RArray.leaf b);
      let rp_1 := CommRing.Poly.num 0;
      let re_1 := (CommRing.Expr.var 0).add (CommRing.Expr.var 1);
      let re_2 := (CommRing.Expr.var 1).add (CommRing.Expr.var 0);
      diseq_unsat ctx
        (diseq_norm ctx e_2 e_1 p_1 (eagerReduce (Eq.refl true))
          (CommRing.diseq_norm rctx re_1 re_2 rp_1 (eagerReduce (Eq.refl true)) h))
-/
#guard_msgs in
open Linarith in
set_option trace.grind.debug.proof true in
example [CommRing α] [LE α] [LT α] [IsPreorder α] [OrderedRing α] (a b : α)
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
example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : b ≥ 0 → c > b → d > b → a ≠ b + c → a > b + c → a < b + d →  False := by
  grind

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : a ≤ b → a ≥ c + d → d = 0 → b = c → a = b := by
  grind

example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b c d : α)
    : a ≤ b → a ≥ c + d → d ≤ 0 → d ≥ 0 → b = c → a = b := by
  grind

open Linarith RArray
set_option trace.grind.debug.proof true in
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (a b c d : α)
    : a ≤ b → a - c ≥ 0 + d → d ≤ 0 → d ≥ 0 → b = c → a ≠ b → False := by
  grind

example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c : α)
    : a + 2*b = 0 → c + b = -b → a = c := by
  grind

example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c : α)
    : a + 2*b = 0 → a = c → c + b = -b := by
  grind

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (a b c : α)
    : c = a → a + b ≤ 3 → 3 ≤ b + c → a + b = 3 := by
  grind

/--
trace: [grind.linarith.model] a := 7/2
[grind.linarith.model] b := 1
[grind.linarith.model] c := 2
[grind.linarith.model] d := 3
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.linarith.model true in
example [CommRing α] [LE α] [LT α] [IsLinearOrder α] [OrderedRing α] (a b c d : α)
    : b ≥ 0 → c > b → d > b → a ≠ b + c → a > b + c → a < b + d →  False := by
  grind

/--
trace: [grind.linarith.model] a := 0
[grind.linarith.model] b := 1
[grind.linarith.model] c := 1
[grind.linarith.model] d := -1
-/
#guard_msgs (drop error, trace) in
set_option trace.grind.linarith.model true in
example [IntModule α] [LE α] [LT α] [IsLinearOrder α] [OrderedAdd α] (a b c d : α)
    : a ≤ b → a - c ≥ 0 + d → d ≤ 0 → b = c → a ≠ b → False := by
  grind

/-- trace: [grind.split] x = 0, generation: 0 -/
#guard_msgs (trace) in
set_option trace.grind.split true in
example [IntModule α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedAdd α] (f : α → α) (x : α)
    : Zero.zero ≤ x → x ≤ 0 → f x = a → f 0 = a := by
  grind

-- should not split on `x = 0` since `α` is not a linear order
#guard_msgs (drop error, trace) in
set_option trace.grind.split true in
example [IntModule α] [LE α] [LT α] [Preorder α] [OrderedAdd α] (f : α → α) (x : α)
    : Zero.zero ≤ x → x ≤ 0 → f x = a → f 0 = a := by
  grind

example [CommRing α] [LE α] [LT α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α] (f : α → α → α) (x y z : α)
    : z ≤ x → x ≤ 1 → z = 1 → f x y = 2 → f 1 y = 2 := by
  grind
