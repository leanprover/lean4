import tactic
(*
simple_tac = Cond(function(env, ios, s)
                     local gs = s:goals()
                     local n, g = gs:head()
                     local r = g:conclusion():is_and()
                     print ("Cond result: " .. tostring(r))
                     return r
                  end,
                  Then(apply_tac("and_intro"), assumption_tac()),
                  Then(apply_tac("or_introl"), assumption_tac()))

simple2_tac = When(function(env, ios, s)
                      local gs = s:goals()
                      local n, g = gs:head()
                      local r = g:conclusion():is_and()
                      print ("When result: " .. tostring(r))
                      return r
                   end,
                   apply_tac("and_intro"))
*)
theorem T1 (a b c : Bool) : a -> b -> c -> a ∧ b.
  (* simple_tac *)
  done

theorem T2 (a b : Bool) : a -> a ∨ b.
  (* simple_tac *)
  done

theorem T4 (a b c : Bool) : a -> b -> c -> a ∧ b.
  (* simple2_tac *)
  exact
  done

theorem T5 (a b c : Bool) : a -> b -> c -> a ∨ b.
  (* simple2_tac *)
  apply or_introl
  exact
  done
