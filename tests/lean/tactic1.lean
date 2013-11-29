Variables p q r : Bool

(**
 local env = get_environment()
 local conjecture = parse_lean('p => q => p && q')
 local tac = REPEAT(conj_tactic() ^ imp_tactic()) .. assumption_tactic()
 local proof = tac:solve(env, context(), conjecture)
 env:add_theorem("T1", conjecture, proof)
**)

Show Environment 1.
