function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(env:normalize(env:type_check(t))))
end

local A          = Local("A", Bool)
local env        = environment()
local retraction = Const("retraction")

env = add_inductive(env,
                    "retraction", Bool,
                    "inj", Pi(A, retraction))

local u = global_univ("u")
env = env:add_universe("u")
local a = Local("a", Bool)
local r = Local("r", retraction)

local rec = Const("retraction_rec")
display_type(env, rec)
local proj = Fun(r, rec(Bool, Fun(a, a), r))
local inj  = Const("inj")

assert(not pcall(function() display_type(env, Fun(a, proj(inj(a)))) end))
