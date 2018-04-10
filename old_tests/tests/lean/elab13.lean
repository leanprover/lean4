open tactic list

#check
assume c : name,
(
do {
   env  ← get_env,
   decl ← returnex (environment.get env c),
   num  ← return (length (declaration.univ_params decl)),
   ls   ← mk_num_meta_univs 2,
   return (expr.const c ls)

} : tactic expr)
