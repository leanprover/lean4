local env = environment()
local nat = Const("nat")

env = add_inductive(env,
                    "nat", Type,
                    "zero", nat,
                    "succ", mk_arrow(nat, nat))

-- Display all declarations in the environment
env:for_each_decl(function(d)
                     print(tostring(d:name()) .. " : " .. tostring(d:type()))
                  end
)
