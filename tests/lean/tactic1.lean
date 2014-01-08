variables p q r : Bool

(*
 local env = get_environment()
 local conjecture = parse_lean('p → q → p && q')
 local tac = Repeat(conj_tac() ^ imp_tac() ^ assumption_tac())
 local proof = tac:solve(env, context(), conjecture)
 env:add_theorem("T1", conjecture, proof)
*)

print environment 1.
