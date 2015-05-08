import data.nat.basic
open nat

definition two1 : nat := 2
definition two2 : nat := succ (succ (zero))
definition f (x : nat) (y : nat) := y
constant g : nat → nat → nat
constants a b : nat

(*
local tc     = type_checker_with_hints(get_env())
local plugin = whnf_match_plugin(tc)
function tst_match(p, t)
   local r1, r2   = match(p, t, plugin)
   assert(r1)
   print("--------------")
   for i = 1, #r1 do
      print("  expr:#" .. i .. " := " .. tostring(r1[i]))
   end
   for i = 1, #r2 do
      print("  lvl:#" .. i .. "  := " .. tostring(r2[i]))
   end
end

local nat  = Const("nat")
local f    = Const("f")
local g    = Const("g")
local a    = Const("a")
local b    = Const("b")
local x    = mk_idx_meta(0, nat)
local p    = g(x, f(x, a))
local t    = g(a, f(b, a))
tst_match(p, t)
tst_match(f(x, x), f(a, b))
*)
