import data.list
open tactic list expr

private meta_definition pattern_telescope (e : expr) (ps : list expr) : tactic (list expr × expr × expr) :=
if expr.is_pi e = tt then do
   n : name     ← mk_fresh_name,
   p : expr     ← return $ local_const n (binding_name e) (binding_info e) (binding_domain e),
   new_e : expr ← return $ instantiate_var (binding_body e) p,
   pattern_telescope new_e (p :: ps)
else do
  (lhs, rhs) ← match_eq e,
  return (reverse ps, lhs, rhs)

meta_definition mk_pattern_for_constant (n : name) : tactic pattern :=
do env : environment  ← get_env,
   d   : declaration  ← returnex $ environment.get env n,
   ls  : list level   ← return $ map level.param (declaration.univ_params d),
   (some (type:expr)) ← return $ declaration.instantiate_type_univ_params d ls | failed,
   (es, lhs, rhs)     ← pattern_telescope type [],
   p   : pattern      ← mk_pattern ls es lhs [rhs, app_of_list (expr.const n ls) es],
   return p

open nat

example (a b : nat) (H : a + b + a + b = 0) : true :=
by do
  a ← get_local `a, b ← get_local `b,
  H ← get_local `H >>= infer_type,
  (lhs, rhs) ← match_eq H,
  p ← mk_pattern_for_constant $ `add.comm,
  [rhs_inst, prf] ← match_pattern p lhs | failed,
  trace "match rhs",
  trace rhs_inst,
  trace "proof lhs = rhs",
  trace prf,
  prf_type ← infer_type prf,
  trace "proof type:",
  trace prf_type,
  constructor
