import Std.Tactic.BVDecide

set_option trace.Meta.Tactic.bv true in
set_option trace.profiler true in
example (x y : BitVec 13) : 11 *  ~~~(x &&&  ~~~y) - 9 *  ~~~(x ||| y) + 2 * (x &&&  ~~~y) = 2 *  ~~~y + 11 * y := by
  bv_decide


--example (x y : BitVec 13)
--  (h : (!11#13 * ~~~(x &&& ~~~y) + (~~~(9#13 * (~~~x &&& ~~~y)) + 1#13) + (x &&& ~~~y) <<< 1 == ~~~y <<< 1 + 11#13 * y) = true)
--  : False := by
--    bv_decide
--
--
--set_option trace.Meta.Tactic.bv true in
--set_option trace.profiler true in
--example :
--∀ (x_0 x_1 : BitVec 13),
--  (!let_fun _let0 := ~~~x_1;
--      let_fun _let1 := BitVec.extractLsb 11 0 _let0;
--      !x_1 * 11#13 + (_let1 ++ 0#1) + 9#13 * (_let0 &&& ~~~x_0) ==
--          11#13 * ~~~(x_0 &&& _let0) + ((_let1 &&& BitVec.extractLsb 11 0 x_0) ++ 0#1)) =
--    true := by
--  intros
--  bv_normalize
--  sorry
--  bv_decide
