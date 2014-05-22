
local env = environment()
local u   = param_univ("u")
local Set = Const("Set", {u})
local A   = Local("A", mk_sort(u))

env = add_inductive(env,
                     "Set", {u}, 0, mk_sort(u+1),
                     "sup", Pi(A, mk_arrow(mk_arrow(A, Set), Set)))

local env = environment()
local u   = param_univ("u")
local Set = Const("Set", {u})
local A   = Local("A", mk_sort(u))

env = add_inductive(env,
                    "Set", {u}, 1, Pi(A, mk_sort(u+1)),
                    "sup", Pi(A, mk_arrow(mk_arrow(A, Set(A)), Set(A))))
