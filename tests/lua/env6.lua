local env = bare_environment()
env = add_decl(env, mk_constant_assumption("A", Prop))
local A   = Const("A")
local x   = Local("x", Prop)
env = add_decl(env, mk_axiom("magic", Pi(x, x)))
local saved_env = env
env = add_decl(env, mk_axiom("Ax", A))
env = add_decl(env, mk_definition("T1", A, Const("Ax")))
-- The check mk_theorem("Ax", A, Const("T1")) failes because env
-- contains the axiom named Ax.
-- So, we cannot transform Ax into a theorem that depends on itself.
-- (This is good)
assert(not pcall(function() env:replace(check(env, mk_theorem("Ax", A, Const("T1")))) end))
assert(env:find("Ax"):is_axiom())
local magic = Const("magic")
-- Replace axiom Ax with the theorem Ax that is checked in the old
-- environment saved_env. Everything works because env is a descendant
-- of saved_env
env = env:replace(check(saved_env, mk_theorem("Ax", A, magic(A))))
assert(not env:find("Ax"):is_axiom())
assert(env:find("Ax"):is_theorem())
