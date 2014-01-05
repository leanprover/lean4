(**
 -- This example demonstrates how to create a new tactic using Lua.
 -- The basic idea is to reimplement the tactic conj_tactic in Lua.

 -- Tactic for splitting goals of the form
 --      n : Hs |- A /\ B
 -- into
 --      n::1 : Hs |- A
 --      n::2 : Hs |- B
 function conj_fn(env, ios, s)
    local gs = s:goals()
    -- We store the information needed by the proof_builder in the
    -- array proof_info.
    -- proof_info has the format {{name_1, expr_1}, ... {name_k, expr_k}}
    -- where name_i is a goal splitted by this tactic, and expr_i
    -- is the conclusion of the theorem, that is, an expression of the form
    --     A /\ B
    local proof_info = {}
    -- We store the new goals into the Lua array new_gs.
    -- new_gs has the format {{name_1, goal_1}, ..., {name_n, goal_n}}
    local new_gs     = {}
    local found = false
    for n, g in gs:pairs() do
       yield() -- Give a chance to other tactics to run
       local c = g:conclusion()
       if c:is_and() then
          -- Goal g is of the form Hs |- A /\ B
          found = true -- The tactic managed to split at least one goal
          local Hs = g:hypotheses()
          local A  = c:arg(1)
          local B  = c:arg(2)
          proof_info[#proof_info + 1] = {n, c} -- Save information for implementing the proof builder
          new_gs[#new_gs + 1]   = {name(n, 1), goal(Hs, A)} -- Add goal n::1 : Hs |- A
          new_gs[#new_gs + 1]   = {name(n, 2), goal(Hs, B)} -- Add goal n::1 : Hs |- B
       else
          new_gs[#new_gs + 1]   = {n, g} -- Keep the goal
       end
    end
    if not found then
       return nil -- Tactic is not applicable
    end
    local pb     = s:proof_builder()
    local new_pb =
       function(m, a)
          local Conj  = Const("Conj")
          local new_m = proof_map(m) -- Copy proof map m
          for _, p in ipairs(proof_info) do
             local n = p[1]  -- n is the name of the goal splitted by this tactic
             local c = p[2]  -- c is the conclusion of the goal splitted by this tactic
             assert(c:is_and()) -- c is of the form A /\ B
             -- The proof for goal n is
             --      Conj(A, B, H1, H2)
             -- where H1 and H2 are the proofs for goals n::1 and n::2
             new_m:insert(n, Conj(c:arg(1), c:arg(2), m:find(name(n, 1)), m:find(name(n, 2))))
             -- We don't need the proofs for n::1 and n::2 anymore
             new_m:erase(name(n, 1))
             new_m:erase(name(n, 2))
          end
          return pb(new_m, a) -- Apply the proof builder for the original state
       end
    return  proof_state(s, goals(new_gs), proof_builder(new_pb))
 end
 conj_in_lua = tactic(conj_fn) -- Create a new tactic object using the Lua function conj_fn
 -- Now, the tactic conj_in_lua can be used when proving theorems in Lean.
**)

Theorem T (a b : Bool) : a => b => a /\ b := _.
   (** Then(Repeat(OrElse(imp_tac(), conj_in_lua)), assumption_tac()) **)
   done

-- Show proof created using our script
Show Environment 1.
