-- Define macros for simplifying Tactic creation
local unary_combinator = function (name, fn) tactic_macro(name, { macro_arg.Tactic }, function (env, t) return fn(t) end) end
local nary_combinator = function (name, fn) tactic_macro(name, { macro_arg.Tactics }, function (env, ts) return fn(unpack(ts)) end) end
local const_tactic = function (name, fn) tactic_macro(name, {}, function (env) return fn() end) end

unary_combinator("Repeat", Repeat)
unary_combinator("Try", Try)
nary_combinator("Then", Then)
nary_combinator("OrElse", OrElse)
const_tactic("exact", assumption_tac)
const_tactic("trivial", trivial_tac)
const_tactic("absurd", absurd_tac)
const_tactic("conj_hyp", conj_hyp_tac)
const_tactic("disj_hyp", disj_hyp_tac)
const_tactic("unfold_all", unfold_tac)
const_tactic("beta", beta_tac)
tactic_macro("apply", { macro_arg.Expr }, function (env, e) return apply_tac(e) end)
tactic_macro("unfold", { macro_arg.Id }, function (env, id) return unfold_tac(id) end)

tactic_macro("simp", { macro_arg.Ids },
             function (env, ids)
                return simp_tac(ids)
             end
)
