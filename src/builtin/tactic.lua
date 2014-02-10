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
const_tactic("id", id_tac)
const_tactic("absurd", absurd_tac)
const_tactic("conj_hyp", conj_hyp_tac)
const_tactic("disj_hyp", disj_hyp_tac)
const_tactic("unfold_all", unfold_tac)
const_tactic("beta", beta_tac)
tactic_macro("apply", { macro_arg.Expr }, function (env, e) return apply_tac(e) end)
tactic_macro("unfold", { macro_arg.Id }, function (env, id) return unfold_tac(id) end)

tactic_macro("simp", { macro_arg.Ids },
             function (env, ids)
                if #ids == 0 then
                   ids[1] = "default"
                end
                return simp_tac(ids)
             end
)

tactic_macro("simp_no_assump", { macro_arg.Ids },
             function (env, ids)
                if #ids == 0 then
                   ids[1] = "default"
                end
                return simp_tac(ids, options({"simp_tac", "assumptions"}, false))
             end
)

-- Create a 'bogus' tactic that consume all goals, but it does not create a valid proof.
-- This tactic is useful for momentarily ignoring/skipping a "hole" in a big proof.
-- Remark: the kernel will not accept a proof built using this tactic.
skip_tac = tactic(function (env, ios, s)
                     local gs       = s:goals()
                     local pb       = s:proof_builder()
                     local buggy_pr = mk_constant("invalid proof built using skip tactic")
                     local new_pb   =
                        function(m, a)
                           -- We provide a "fake/incorrect" proof for all goals in gs
                           local new_m = proof_map(m) -- Copy proof map m
                           for n, g in gs:pairs() do
                              new_m:insert(n, buggy_pr)
                           end
                           return pb(new_m, a)
                        end
                     local new_gs = {}
                     return  proof_state(s, goals(new_gs), proof_builder(new_pb))
                  end)

const_tactic("skip", function() return skip_tac end)
