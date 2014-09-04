import data.nat
open nat

definition two1 : nat := 2
definition two2 : nat := succ (succ (zero))
variable f      : nat → nat → nat

(*
local tc     = type_checker_with_hints(get_env(), true)
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

local f    = Const("f")
local two1 = Const("two1")
local two2 = Const("two2")
local succ = Const({"succ"})
tst_match(f(succ(mk_var(0)), two1), f(two2, two2))
*)
