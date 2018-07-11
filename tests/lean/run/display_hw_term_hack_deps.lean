import init.lean.parser.syntax
import init.lean.parser.parsec
import init.lean.ir.type_check init.lean.ir.ssa_check init.lean.ir.elim_phi init.lean.ir.parser

open tactic

meta def is_eqn_theorem : name → bool
| (name.mk_string (name.mk_string "equations" _) _) := tt
| _                                                 := ff

#exit

meta def display_hw_term_hack_dependencies : tactic unit :=
do env ← get_env,
   env.fold (return mk_name_set) $ λ d tac, do {
     s ← tac,
     if is_eqn_theorem d.to_name then return s
     else d.value.mfold s $ λ e _ s, do
       if !e.is_constant_of `wf_term_hack || s.contains d.to_name then return s
       else trace d.to_name >> return (s.insert d.to_name) },
   return ()

-- Uncomment following line to inspect all declarations that use wf_term_hack
-- #eval display_hw_term_hack_dependencies
