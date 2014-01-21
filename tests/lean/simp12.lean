variables a b c d e f : Nat
rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_comm Nat::add_left_comm Nat::distributer Nat::distributel : simple
(*
local opts   = options({"simplifier", "single_pass"}, true)
local t      = parse_lean("f + (c + f + d) + (e * (a + c) + (d + a))")
print(t)
for i = 1, 10 do
  local t2, pr = simplify(t, "simple", get_environment(), context(), opts)
  print("i: " .. i .. " ====>")
  print(t2)
  if t == t2 then
    break
  end
  t = t2
end
*)

