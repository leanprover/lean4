local env = bare_environment()
env = add_decl(env, mk_var_decl("or", mk_arrow(Bool, Bool, Bool)))
env = add_decl(env, mk_var_decl("A", Bool))
local Or = Const("or")
local A  = Const("A")
local B  = Const("B")
local tc = type_checker(env)
local F = Or(A, B)
assert(tc:infer(F) == Bool)
assert(not pcall(function()
                    -- The following test must fail since B is not
                    -- declared in env.
                    -- This test make sure that infer and check are
                    -- not sharing the same cache.
                    print(tc:check(F))
                 end
))
