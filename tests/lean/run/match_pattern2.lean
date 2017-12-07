open tactic list expr

private meta definition pattern_telescope : expr → list expr → tactic (list expr × expr × expr)
| e ps :=
if expr.is_pi e = tt then do
   n      ← mk_fresh_name,
   p      ← return $ local_const n (binding_name e) (binding_info e) (binding_domain e),
   new_e  ← return $ instantiate_var (binding_body e) p,
   pattern_telescope new_e (p :: ps)
else do
  (lhs, rhs) ← match_eq e,
  return (reverse ps, lhs, rhs)

meta definition mk_pattern_for_constant : name → tactic pattern
| n :=
do env ← get_env,
   d   : declaration  ← returnex $ environment.get env n,
   ls  : list level   ← return $ map level.param (declaration.univ_params d),
   (some type)        ← return $ declaration.instantiate_type_univ_params d ls | failed,
   (es, lhs, rhs)     ← pattern_telescope type [],
   p   : pattern      ← mk_pattern ls es lhs [] [rhs, app_of_list (expr.const n ls) es],
   return p

open nat

constant add.comm (a b : nat) : a + b = b + a

example (a b : nat) (H : a + b + a + b = 0) : true :=
by do
  a ← get_local `a, b ← get_local `b,
  H ← get_local `H >>= infer_type,
  (lhs, rhs) ← match_eq H,
  p ← mk_pattern_for_constant $ `add.comm,
  (_, [rhs_inst, prf]) ← match_pattern p lhs | failed,
  trace "match rhs",
  trace rhs_inst,
  trace "proof lhs = rhs",
  trace prf,
  prf_type ← infer_type prf,
  trace "proof type:",
  trace prf_type,
  constructor
