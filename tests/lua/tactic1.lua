local env = environment()
local A = Local("A", Type)
env = add_decl(env, mk_constant_assumption("eq", Pi(A, mk_arrow(A, A, Prop))))
local eq = Const("eq")
local a  = Local("a", A)
local b  = Local("b", A)
local H  = Local("H", eq(A, a, b))
local m  = mk_metavar("m", Pi(A, a, b, H, eq(A, a, b)))(A, a, b, H)
local s  = to_proof_state(m, eq(A, a, b))
local t = Then(Append(trace_tac("tst1a"), trace_tac("tst1b")),
               trace_tac("tst2"),
               Append(trace_tac("tst3"), assumption_tac()))
for r in t(env, s) do
   print("Solution:")
   print(r)
   print("---------")
end
